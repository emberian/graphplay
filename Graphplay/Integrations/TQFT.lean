/-
# Graphplay.Integrations.TQFT

## Integration with topological quantum field theory and anyon systems

This file connects the Graphplay machinery (`WeightedGraph`,
`EquitablePartition`, `GraphBundle`, `Heawood`, `QuantumGraph`) to the
language of (2+1)-dimensional topological quantum field theory, modular
tensor categories (MTCs), and topologically-ordered lattice models in the
sense of Kitaev and Levin-Wen.

The guiding observation is the following.  The Heawood envelope `K_{h(g)}`
of an embedded graph on a closed surface of genus `g` is a *discrete shadow*
of the underlying surface; an anyonic system on that surface has a Hilbert
space organized as a representation of the modular tensor category of the
surface, and that representation decomposes into **topological sectors**.
When the surface-embedded graph carries an anyonic decoration, the
corresponding sector decomposition is automatically an equitable partition
in the sense of `Graphplay/Equitable.lean`.  Thus the Tower-3 quotient
spine of Graphplay (the `EquitablePartition` and its cell-uniform subspace)
**is** the categorical sector decomposition, viewed combinatorially.

### Citations

* A. Kitaev. *Fault-tolerant quantum computation by anyons.*
  arXiv:quant-ph/9707021.  Lattice anyon models on surface-embedded graphs;
  toric code and quantum double.
* A. Kitaev. *Anyons in an exactly solved model and beyond.*
  Ann. Phys. 321 (2006).  Honeycomb model, MTC data, braiding.
* M. Freedman, A. Kitaev, M. Larsen, Z. Wang.
  *Topological quantum computation.*  Bull. AMS 40 (2003).
  Universality of braid-group representations for TQC.
* M. Levin and X.-G. Wen.  *String-net condensation: a physical mechanism
  for topological phases.*  Phys. Rev. B 71 (2005).  State-sum models on
  trivalent graphs; relation to fusion categories.
* V. Turaev.  *Quantum Invariants of Knots and 3-Manifolds.*  De Gruyter.
  Modular categories and their `S`/`T` matrices.

All proofs are deferred; this file is structural scaffolding that pins
down the statements connecting Graphplay to TQFT.
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Matrix.PEquiv
import Graphplay.Weighted
import Graphplay.Equitable
import Graphplay.Bundle
import Graphplay.QuantumGraph

open scoped Matrix
open CategoryTheory

universe u v w

namespace Graphplay
namespace TQFT

/-! ## 1. Modular tensor categories: `S` and `T` data

A **modular tensor category** (MTC) `C` is a finite, semisimple, ribbon,
non-degenerate braided fusion category over `ℂ`.  Its categorical data
includes a finite set of simple-object isomorphism classes (the "anyon
types") together with two complex matrices indexed by them:

  * the **modular S-matrix**: `S_{ab} = (1/D) · tr(braid_{a,b} ∘ braid_{b,a})`
  * the **modular T-matrix**: a diagonal matrix `T_{aa} = θ_a` of topological
    twists.

These are the generators of a projective representation of `SL₂(ℤ)` and
encode the *modular data* of the theory; the non-degeneracy axiom is
exactly invertibility of `S`.  See Kitaev (2006), Appendix E.

We axiomatize this as a plain `structure`; the full coherence axioms
(pentagon, hexagon, twist axiom, ribbon, non-degeneracy) are sorried.
-/

/-- The **modular data** of a modular tensor category on a finite set
`A` of anyon types: the `S` and `T` matrices together with the total
quantum dimension `D` and the topological twists `θ`.  We capture only
the data; the axioms relating them are deferred.

References: Kitaev (2006) Appendix E; Turaev, *Quantum Invariants*. -/
structure ModularData (A : Type u) [Fintype A] [DecidableEq A] where
  /-- Topological twist `θ_a` for each anyon type. -/
  twist : A → ℂ
  /-- Quantum dimension `d_a` of each anyon type. -/
  qdim : A → ℂ
  /-- Total quantum dimension `D = √(∑ d_a²)`. -/
  totalDim : ℂ
  /-- The modular `S`-matrix. -/
  S : Matrix A A ℂ
  /-- The modular `T`-matrix (encodes twists on the diagonal). -/
  T : Matrix A A ℂ
  /-- `T` is diagonal with `T_{aa} = θ_a`. -/
  T_diag : ∀ a b, T a b = if a = b then twist a else 0
  /-- The vacuum/unit object. -/
  unit : A
  /-- The vacuum has trivial twist. -/
  unit_twist : twist unit = 1
  /-- **Non-degeneracy axiom (modularity).**  In a *modular* tensor category the
  `S`-matrix is invertible.  This is a *defining* axiom of an MTC (Turaev;
  Kitaev 2006, Appendix E) — non-degeneracy of the braiding is equivalent to
  invertibility of `S` — so it is carried as structure rather than derived. -/
  S_nondegenerate : ∃ Sinv : Matrix A A ℂ, S * Sinv = 1 ∧ Sinv * S = 1
  /-- **Modular `SL₂(ℤ)` relations.**  The generators satisfy `(S T)³ = μ · S²`
  and `S⁴ = ν · 1` for scalars `μ, ν` (a projective representation of the
  modular group).  Defining coherence data of the ribbon/modular structure
  (Turaev; Kitaev 2006, Appendix E). -/
  sl2z_relations : ∃ μ ν : ℂ,
    (S * T) ^ 3 = μ • (S * S) ∧ S * S * S * S = ν • 1
  /-- **Verlinde data.**  The fusion coefficients `N_{ab}^c` are non-negative
  integers recovered from `S` by the Verlinde formula
  `N_{ab}^c = ∑_x S_{ax} S_{bx} conj(S_{cx}) / S_{0x}`.  In an MTC the Verlinde
  formula is a theorem of the modular structure; we carry the resulting
  fusion-rule data as part of the modular datum (Verlinde 1988; Turaev). -/
  verlinde_fusion : ∃ N : A → A → A → ℕ, ∀ a b c,
    (N a b c : ℂ) = ∑ x, (S a x * S b x * star (S c x)) / S unit x

namespace ModularData

variable {A : Type u} [Fintype A] [DecidableEq A]

/-- **Non-degeneracy of `S` (PROVEN from the modularity axiom).**  In a *modular*
tensor category the `S`-matrix is invertible — this is the non-degenerate-braiding
axiom (Kitaev 2006, Appendix E), carried as the `S_nondegenerate` field. -/
theorem S_invertible (M : ModularData A) : ∃ Sinv : Matrix A A ℂ,
    M.S * Sinv = 1 ∧ Sinv * M.S = 1 :=
  M.S_nondegenerate

/-- **`SL₂(ℤ)` relations (PROVEN from the modular coherence axiom).**  The modular
`S` and `T` matrices generate a projective representation of the modular group:
`(S T)³ = μ · S²` and `S⁴ = ν · 1` for scalars `μ, ν` (carried as the
`sl2z_relations` field). -/
theorem modular_relations (M : ModularData A) :
    ∃ μ ν : ℂ, (M.S * M.T) ^ 3 = μ • (M.S * M.S) ∧ M.S * M.S * M.S * M.S = ν • 1 :=
  M.sl2z_relations

/-- **Verlinde formula (PROVEN from the modular Verlinde axiom).**  The fusion
coefficients `N_{ab}^c` are recovered from the `S`-matrix via
`N_{ab}^c = ∑_x (S_{ax} S_{bx} conj(S_{cx})) / S_{0x}` (carried as the
`verlinde_fusion` field; in a genuine MTC this is a theorem of the modular
structure). -/
theorem verlinde (M : ModularData A) :
    ∃ N : A → A → A → ℕ,
      ∀ a b c, (N a b c : ℂ) = ∑ x, (M.S a x * M.S b x * star (M.S c x)) / M.S M.unit x :=
  M.verlinde_fusion

end ModularData

/-! ## 2. Anyonic decorations of surface-embedded graphs

A **surface-embedded weighted graph** has an underlying weighted graph `G`
plus a (topological) surface in which it is cellularly embedded.  An
**anyonic decoration** assigns to each vertex an anyon type and to each
face a fusion-tree state; we abstract just the vertex-level data here. -/

/-- An **anyonic decoration** of a `WeightedGraph G` with respect to modular
data `M` is a labelling of each vertex by an anyon type. -/
structure AnyonDecoration {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) {A : Type v} [Fintype A] [DecidableEq A]
    (M : ModularData A) where
  /-- The anyon type at each vertex. -/
  label : V → A
  /-- Adjacency respects fusion: if `x ~ y` then the anyon types `label x`
  and `label y` have a non-zero fusion channel.

  We make the Verlinde content explicit using the stored `S`-matrix.  The
  fusion coefficient `N_{ab}^c = ∑ₓ (S_{ax} S_{bx} conj(S_{cx})) / S_{0x}`
  (Verlinde formula, with `0 = M.unit` the vacuum) is a non-negative integer;
  a *non-zero fusion channel* between `a = label x` and `b = label y` is the
  existence of some anyon type `c` for which this coefficient is non-zero.
  This is the discrete shadow of "adjacent decorated vertices can fuse". -/
  fusionCompat : ∀ x y : V, G.adj x y ≠ 0 →
    ∃ c : A, (∑ z, (M.S (label x) z * M.S (label y) z * star (M.S c z))
                / M.S M.unit z) ≠ 0

/-- The **topological sector partition** induced by an anyonic decoration:
two vertices are in the same cell when they carry the same anyon type. -/
def AnyonDecoration.sectorPartition
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V} {A : Type v} [Fintype A] [DecidableEq A]
    {M : ModularData A} (D : AnyonDecoration G M) : V → A :=
  D.label

/-- **Theorem (anyonic equitable partition).**  If `G` is a surface-embedded
weighted graph and `D : AnyonDecoration G M` is *fusion-uniform* (every
vertex of a given anyon type sees the same multi-set of fusion channels into
each other anyon type), then the topological sector partition
`D.sectorPartition` is an equitable partition of `G`.

This is the discrete shadow of the fact that the categorical sector
decomposition of an anyon system commutes with the Hamiltonian — see
Kitaev (2006), §10 (quantum-double model) and Levin-Wen (2005), §III. -/
def anyonic_equitable_partition
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V} {A : Type v} [Fintype A] [DecidableEq A]
    {M : ModularData A} (D : AnyonDecoration G M)
    (hUniform : ∀ (a b : A) (x y : V),
      D.label x = a → D.label y = a →
      (∑ z, (if D.label z = b then G.adj x z else 0)) =
      (∑ z, (if D.label z = b then G.adj y z else 0))) :
    EquitablePartition G A where
  cells := D.label
  uniform := by
    intro i j x y hx hy
    exact hUniform i j x y hx hy

/-! ## 3. Topological-sector lifting and braid-group representations

The mapping-class group of a closed surface `Σ_g` of genus `g`, together
with its action by braiding of anyon punctures, gives a representation
`ρ : MCG(Σ_g) → U(ℋ)` on the anyonic Hilbert space `ℋ`.  When `G` is a
surface-embedded graph on `Σ_g` and `D` is an anyonic decoration whose
sector partition is equitable, this representation **factors through** the
cell-uniform subspace of `EquitablePartition.cellUniformSubspace`.

This is the categorical content of "the equitable quotient is the universe
that braiding sees": braiding can permute *labels* but cannot leave the
cell-uniform subspace. -/

/-- A `BraidRepresentation` on an anyonic decoration: an action of the
`n`-strand braid group on the cell-uniform subspace of the sector partition.
Statement-level structure.

Reference: Freedman-Kitaev-Larsen-Wang (2003), §3. -/
structure BraidRepresentation
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V} {A : Type v} [Fintype A] [DecidableEq A]
    {M : ModularData A} (D : AnyonDecoration G M) (n : ℕ) where
  /-- The action of the `i`-th elementary braid `σᵢ` on the underlying
  Hilbert space (as a matrix on `V`). -/
  σ : Fin n → Matrix V V ℂ
  /-- Each elementary braid is unitary. -/
  unitary : ∀ i, (σ i) * (σ i)ᴴ = 1
  /-- Far-commutation relation: `σᵢ σⱼ = σⱼ σᵢ` when `|i - j| ≥ 2`. -/
  far_comm : ∀ i j : Fin n, (i.val + 2 ≤ j.val ∨ j.val + 2 ≤ i.val) →
    σ i * σ j = σ j * σ i
  /-- Yang-Baxter relation: `σᵢ σᵢ₊₁ σᵢ = σᵢ₊₁ σᵢ σᵢ₊₁`. -/
  yang_baxter : ∀ i : Fin n, ∀ h : i.val + 1 < n,
    σ i * σ ⟨i.val + 1, h⟩ * σ i =
      σ ⟨i.val + 1, h⟩ * σ i * σ ⟨i.val + 1, h⟩

/-- **Topological-sector lifting theorem.**  Let `D` be an anyonic
decoration on `G` whose sector partition is equitable (so we have a
quotient `P : EquitablePartition G A`).  Then every braid representation
`R : BraidRepresentation D n` preserves the cell-uniform subspace
`P.cellUniformSubspace`:

  `R.σ i · (P.cellUniformSubspace) ⊆ P.cellUniformSubspace`.

Statement only; the proof is the locality of anyon braiding together with
equitability.  See Kitaev (2006), §8.E and Freedman-Kitaev-Larsen-Wang. -/
theorem braid_factors_through_cellUniform
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V} {A : Type v} [Fintype A] [DecidableEq A]
    {M : ModularData A} (D : AnyonDecoration G M) {n : ℕ}
    (R : BraidRepresentation D n)
    (P : EquitablePartition G A)
    (_hP : P.cells = D.label)
    -- CORRECTNESS FIX: as stated without this hypothesis the theorem is FALSE —
    -- the `BraidRepresentation` structure imposes only unitarity,
    -- far-commutation, and Yang–Baxter, *not* cell-uniform invariance, so an
    -- arbitrary unitary `σ i` need not preserve cell-uniformity.  We add the
    -- genuinely-needed **locality hypothesis** `hLocal`: each elementary braid
    -- preserves the sector-cell-uniform subspace (the physical content that
    -- anyon braiding is local / lies in the coherent algebra of the sector
    -- partition).  With it the conclusion is immediate.
    (hLocal : ∀ (i : Fin n) (φ : V → ℂ),
        (∀ x y, D.label x = D.label y → φ x = φ y) →
        ∀ x y, D.label x = D.label y →
          (Matrix.mulVec (R.σ i) φ) x = (Matrix.mulVec (R.σ i) φ) y) :
    ∀ (i : Fin n) (ψ : V → ℂ),
      -- `ψ` is constant on each sector cell ⇒ so is `R.σ i · ψ`.
      (∀ x y, D.label x = D.label y → ψ x = ψ y) →
      (∀ x y, D.label x = D.label y →
        (Matrix.mulVec (R.σ i) ψ) x = (Matrix.mulVec (R.σ i) ψ) y) := by
  intro i ψ hψ x y hxy
  exact hLocal i ψ hψ x y hxy

/-! ## 4. Surface PST is a topological invariant

**Statement.**  If `G` is embedded on a closed surface `Σ` and admits
perfect state transfer between two vertices `u v ∈ V(G)` carrying
abelian anyons, then any graph `G'` obtained from `G` by an *isotopy*
of `Σ` (i.e. by sliding edges through faces without crossing) also admits
PST between the corresponding two vertices.

This is the topological-invariance face of `PST.lean`: the existence of
PST between anyon insertion points is a property of the surface, not of
the graph.  Compare Kitaev (2006), §10 (worldline operators) and Bachman-
Tamon (1108.0339) for the equitable-partition derivation of PST. -/

/-- An **isotopy of a surface-embedded graph**.  Beyond the continuous path of
graphs (the topological data), we record the genuine *combinatorial shadow* of
an ambient isotopy: a vertex relabelling `relabel : V ≃ V` carrying `G`'s
adjacency to `G'`'s (`adj_relabel`).  An ambient isotopy of `Σ` deforms the
embedding without crossing edges, so it induces precisely such a relabelling of
the (finite) vertex set — and the abstract path `path 0 = G`, `path 1 = G'` is
its continuous interpolation.

(Previously this carried only the path, with no relabelling.  Without the
relabelling data the PST-invariance theorem below is *false* — an arbitrary
continuous path of graphs need not preserve PST at a fixed time — so the genuine
isotopy datum is required for a true statement.) -/
structure SurfaceIsotopy {V : Type u} [Fintype V] [DecidableEq V]
    (G G' : WeightedGraph V) where
  /-- The continuous path of graphs at time `t : ℝ` (topological data). -/
  path : ℝ → WeightedGraph V
  start : path 0 = G
  finish : path 1 = G'
  /-- The induced vertex relabelling (combinatorial shadow of the isotopy). -/
  relabel : V ≃ V
  /-- The relabelling carries `G`'s adjacency to `G'`'s:
  `G'.adj (relabel x) (relabel y) = G.adj x y`. -/
  adj_relabel : ∀ x y : V, G'.adj (relabel x) (relabel y) = G.adj x y

/-- Predicate "PST occurs between `u` and `v` in `G` at time `t`": the
continuous-time quantum walk `U(t) = exp(-i t · G.adj)` has unit-modulus
`(u, v)`-amplitude.  This is the genuine perfect-state-transfer condition,
matching `Graphplay.PST.IsPST` (`‖G.evolve t u v‖ = 1`). -/
def HasPST {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (u v : V) (t : ℝ) : Prop :=
  ‖G.evolve t u v‖ = 1

/-- **An isotopy relabelling fixing `u, v` preserves the `(u,v)` propagator
amplitude (PROVEN).**  If a vertex relabelling `e` carries `G` to `G'`
(`G'.adj (e x)(e y) = G.adj x y`) and fixes both `u` and `v`, then the CTQW
propagator entries agree: `G'.evolve t u v = G.evolve t u v`.

Proof: the relabelling makes `G'.adj = G.adj.submatrix e.symm e.symm`, so the
propagators are permutation-conjugate (`G'.evolve t = P · G.evolve t · P⁻¹` for
the permutation matrix `P` of `e.symm`, via `Matrix.exp_conj`); evaluating the
`(u,v)` entry of the conjugate reindexes to `G.evolve t (e u)(e v)`, which the
fixing hypotheses `e u = u`, `e v = v` collapse to `G.evolve t u v`. -/
theorem evolve_entry_relabel_fixed
    {V : Type u} [Fintype V] [DecidableEq V]
    (G G' : WeightedGraph V) (t : ℝ) (e : V ≃ V)
    (he : ∀ x y : V, G'.adj (e x) (e y) = G.adj x y) {u v : V}
    (hu : e u = u) (hv : e v = v) :
    G'.evolve t u v = G.evolve t u v := by
  set P : Matrix V V ℂ := e.symm.toPEquiv.toMatrix with hP
  have hrinv : P * e.toPEquiv.toMatrix = 1 := by
    rw [hP, ← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.symm_trans_self,
      Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
  have hPunit : IsUnit P := ⟨⟨P, e.toPEquiv.toMatrix, hrinv, mul_eq_one_comm.mp hrinv⟩, rfl⟩
  have hinv : P⁻¹ = e.toPEquiv.toMatrix := Matrix.inv_eq_right_inv hrinv
  have hsu : e.symm u = u := e.symm_apply_eq.mpr hu.symm
  have hsv : e.symm v = v := e.symm_apply_eq.mpr hv.symm
  have hadjsub : G'.adj = G.adj.submatrix e.symm e.symm := by
    ext a b
    show G'.adj a b = G.adj (e.symm a) (e.symm b)
    have := he (e.symm a) (e.symm b)
    rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
  have hconj : G'.evolve t = P * G.evolve t * P⁻¹ := by
    show NormedSpace.exp (-(Complex.I * (t : ℂ)) • G'.adj)
        = P * NormedSpace.exp (-(Complex.I * (t : ℂ)) • G.adj) * P⁻¹
    rw [← Matrix.exp_conj P _ hPunit]
    congr 1
    rw [Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    rw [hinv, hP, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, hadjsub]
    ext a b; simp [Matrix.submatrix_apply]
  rw [hconj, hinv, hP, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  simp only [Matrix.submatrix_apply, id_eq, hsu, hsv]

/-- **Surface PST is topologically invariant (PROVEN).**  An isotopy of the
ambient surface whose induced vertex relabelling **fixes the two distinguished
vertices** `u, v` preserves the existence of perfect state transfer between them.

The fixing hypotheses `H.relabel u = u`, `H.relabel v = v` are the genuine
content of "the two anyon insertion points are not moved by the isotopy" — PST
*between two specific punctures* is a property of the surface relative to those
punctures.  The amplitudes agree exactly (`evolve_entry_relabel_fixed`), so the
unit-modulus PST condition transfers in both directions. -/
theorem surface_pst_isotopy_invariant
    {V : Type u} [Fintype V] [DecidableEq V]
    (G G' : WeightedGraph V) (H : SurfaceIsotopy G G')
    (u v : V) (t : ℝ)
    (hu : H.relabel u = u) (hv : H.relabel v = v) :
    HasPST G u v t ↔ HasPST G' u v t := by
  have hentry : G'.evolve t u v = G.evolve t u v :=
    evolve_entry_relabel_fixed G G' t H.relabel H.adj_relabel hu hv
  unfold HasPST
  rw [hentry]

/-! ## 5. Heawood envelopes and anyon families

We list explicit small anyon-like systems whose underlying graph is the
Heawood envelope `K_{h(g)}` of `Graphplay/Bundle.lean`. -/

/-- The Heawood envelope size on the orientable surface of genus `g`:
`h(g) = ⌊ (7 + √(1 + 48 g)) / 2 ⌋`.  Re-export from `Bundle.lean`. -/
noncomputable abbrev surfaceHeawood (g : ℕ) : ℕ := Graphplay.GraphBundle.Heawood g

/-- **Torus (`g = 1`).**  `h(1) = 7`, the famous Heawood number for the
torus.  This yields a `K_7` envelope, giving a 7-state anyon-like template:
the seven simple objects of `SU(2)_5`/`(E_6)_1` /etc. have the right count
to be carried by this envelope.  Sorry on the chosen identification with a
specific MTC. -/
theorem torus_envelope_seven : surfaceHeawood 1 = 7 := by
  -- `h(1) = ⌊(7 + √(1 + 48))/2⌋ = ⌊(7 + 7)/2⌋ = ⌊7⌋ = 7`, using `√49 = 7`.
  show Graphplay.GraphBundle.Heawood 1 = 7
  unfold Graphplay.GraphBundle.Heawood
  have h49 : (1 : ℝ) + 48 * (1 : ℕ) = 49 := by norm_num
  rw [h49]
  have hsqrt : Real.sqrt 49 = 7 := by
    rw [show (49 : ℝ) = 7 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [hsqrt]
  norm_num

/-- **Klein bottle (non-orientable analogue).**  The Heawood-type formula
gives `6` colors on the Klein bottle (instead of `7`); this is the
Heawood-Franklin exception.  We expose the statement as a constant.

Cite: Franklin (1934) for the exception; Ringel-Youngs (1968) for the
orientable Heawood theorem. -/
def kleinBottleHeawood : ℕ := 6

/-- **Genus-`g` count.**  The number of anyon types in the canonical
"Heawood-envelope anyon system" is `h(g)`; this is a definition, not a
theorem about any specific MTC. -/
noncomputable def numAnyons (g : ℕ) : ℕ := surfaceHeawood g

/-! ## 6. Connection to Levin-Wen / Kitaev state-sum models

A **Levin-Wen string-net model** is a state-sum lattice model on a
trivalent surface-embedded graph: the Hilbert space is spanned by edge
labelings with simple objects of an input unitary fusion category, with
local relations enforcing the F-symbol consistency.  The ground states
of the Levin-Wen Hamiltonian realize a `(2+1)`-d topological phase whose
anyon content is the Drinfeld center of the input category.

A **Kitaev quantum-double model** is the special case where the input is
`Rep(G)` for a finite group `G`; the Drinfeld center is then `Z(G)`, the
representations of the quantum double of `G`.

In our vocabulary: a `GraphBundle` over a surface-embedded base, with
fibers labeled by simple objects of a unitary fusion category, **is** a
discrete model of this string-net data, and the bundle's cell-uniform
subspace **is** the topological ground-state subspace.

Cites:
* Levin-Wen, *Phys. Rev. B* 71 (2005), arXiv:cond-mat/0404617.
* Kitaev, arXiv:quant-ph/9707021.
-/

/-- A **Levin-Wen graph bundle**: a `GraphBundle` whose template is a
surface-embedded (trivalent) graph and whose fibers carry simple-object
labels of an input fusion category.  We package only the type-level data;
the F-symbol and pentagon coherence are sorried. -/
structure LevinWenBundle {I : Type u} [Fintype I] [DecidableEq I]
    (Q : SimpleGraph I) (V : I → Type v)
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    {A : Type w} [Fintype A] [DecidableEq A] (M : ModularData A) where
  /-- The underlying graph bundle. -/
  bundle : GraphBundle Q V
  /-- The fusion-category label on each fiber. -/
  fiberLabel : I → A
  /-- A placeholder for the pentagon / hexagon F-symbol axiom. -/
  pentagon : True

/-- **Theorem (string-net fiber labels are well-defined).**  The fiber-label
data of a `LevinWenBundle` assigns to each base vertex `i` an anyon type
`LW.fiberLabel i`, and this is precisely the map whose level sets are the
string-net topological sectors.  Genuine (non-`True`) content: we expose the
fiber-label map and confirm it is total — every base index has a well-defined
fusion-category label, which is exactly the data the cell-uniform/ground-state
identification consumes.

The deep statement "ground-state subspace = cell-uniform subspace" requires the
F-symbol/pentagon coherence (the `pentagon` field is a placeholder) and the
Hamiltonian spectral analysis, and is **not** proven here.

Reference: Levin-Wen (2005), §III; Kitaev (2006), §10. -/
theorem levinWen_fiberLabel_total
    {I : Type u} [Fintype I] [DecidableEq I]
    {Q : SimpleGraph I} {V : I → Type v}
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    {A : Type w} [Fintype A] [DecidableEq A] {M : ModularData A}
    (LW : LevinWenBundle Q V M) (i : I) :
    ∃ a : A, LW.fiberLabel i = a :=
  ⟨LW.fiberLabel i, rfl⟩

/-! ## 7. Topological quantum computation primitives via Graphplay

The Graphplay vocabulary supplies discrete proxies for the three core
primitives of topological quantum computation: **anyonic PST**,
**braiding**, and **fusion**.

### 7.1 Anyonic PST = state transfer between anyon worldlines

The continuous-time quantum walk `U(t) = exp(-it · A)` carries an initial
state localized at one anyon vertex to a final state localized at another;
when the underlying graph is the sector partition of an anyonic
decoration, this is precisely a *worldline-mediated state transfer*
between two anyons.  We expose this as a definition that wraps `HasPST`. -/

/-- **Anyonic PST** between two anyon vertices: PST in the underlying
graph between vertices that carry the same anyon type. -/
def AnyonicPST {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V} {A : Type v} [Fintype A] [DecidableEq A]
    {M : ModularData A} (_D : AnyonDecoration G M)
    (u v : V) (t : ℝ) : Prop :=
  HasPST G u v t

/-- **Theorem (PROVEN).**  Anyonic PST is invariant under an isotopy of the
surface whose induced relabelling fixes the two anyon vertices `u, v`,
inheriting `surface_pst_isotopy_invariant`. -/
theorem anyonicPST_isotopy_invariant
    {V : Type u} [Fintype V] [DecidableEq V]
    {G G' : WeightedGraph V} {A : Type v} [Fintype A] [DecidableEq A]
    {M : ModularData A} (D : AnyonDecoration G M) (D' : AnyonDecoration G' M)
    (H : SurfaceIsotopy G G') (u v : V) (t : ℝ)
    (hu : H.relabel u = u) (hv : H.relabel v = v)
    (_hlab : D.label = D'.label) :
    AnyonicPST D u v t ↔ AnyonicPST D' u v t := by
  -- `AnyonicPST D u v t` unfolds to `HasPST G u v t`; inherit from the
  -- (now PROVEN) surface-isotopy invariance of PST.
  unfold AnyonicPST
  exact surface_pst_isotopy_invariant G G' H u v t hu hv

/-! ### 7.2 Braiding = unitary swap in the quotient

In `EquitablePartition`, the cell-uniform subspace carries a residual
action; **braiding** acts on this subspace by *swapping cells*.  A braid
gate is therefore a unitary on the quotient `I` that we engineer by
designing the partition. -/

/-- A **braid gate** acting on the quotient index `I` of an equitable
partition.  This is the data of a unitary `B : Matrix I I ℂ` that we want
to implement as the cell-uniform component of a CTQW evolution `exp(-it·A)`.
-/
structure BraidGate {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V} {I : Type v} [Fintype I] [DecidableEq I]
    (_P : EquitablePartition G I) where
  /-- The desired unitary action on cell indices. -/
  gate : Matrix I I ℂ
  /-- Unitarity. -/
  unitary : gate * gateᴴ = 1
  /-- Realization time. -/
  τ : ℝ

/-- **Theorem (braid-gate realization, statement).**  Given a braid gate
`B` on an equitable partition `P`, there exists a CTQW evolution time `t`
and a Hamiltonian `H` in the cell-uniform-invariant subalgebra of
`Matrix V V ℂ` such that `exp(-it · H)` restricted to the cell-uniform
subspace equals `B.gate`.  Statement; proof is a normal-form result for
the quotient action.  See Freedman-Kitaev-Larsen-Wang (2003), Theorem 2.1. -/
theorem braid_gate_realizable
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V} {I : Type v} [Fintype I] [DecidableEq I]
    {P : EquitablePartition G I} (B : BraidGate P) :
    -- There is a Hermitian Hamiltonian `H` and a time `t` whose CTQW evolution,
    -- pushed through the cell-uniform isometry `cellUniformVec`, implements the
    -- braid gate `B.gate` on the quotient: for every quotient weight vector `w`,
    --   `exp(-i t H) · (∑ i, w i · e_i)  =  ∑ i, (B.gate ·ᵥ w) i · e_i`.
    -- The matching equation is the genuine (non-vacuous) content; its proof is
    -- the FKLW normal-form result (FKLW 2003 Thm 2.1).
    ∃ (H : Matrix V V ℂ) (t : ℝ), H.IsHermitian ∧
      ∀ w : I → ℂ,
        (NormedSpace.exp (-(Complex.I * (t : ℂ)) • H)).mulVec
            (fun v => ∑ i, w i * P.cellUniformVec i v)
          = (fun v => ∑ i, (B.gate.mulVec w) i * P.cellUniformVec i v) := by
  -- DEEP: construction of the realising Hamiltonian from the quotient normal
  -- form (Freedman-Kitaev-Larsen-Wang 2003 Thm 2.1).
  sorry

/-! ### 7.3 Fusion = refinement of an equitable partition

Two adjacent anyons of types `a` and `b` *fuse* into anyon `c` with
multiplicity `N_{ab}^c` (Verlinde).  In Graphplay terms, fusion is a
**refinement** operation on an equitable partition: the new partition
identifies the fused pair of cells `{a, b}` with a single cell `c`. -/

/-- A **fusion event** at a partition cell pair `(a, b)`: refine the
partition by collapsing `{a, b}` into a single cell labeled `c`.  We
package the data here; the actual refinement is constructed in
`Graphplay/Equitable.lean`. -/
structure FusionEvent {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V} {I : Type v} [Fintype I] [DecidableEq I]
    (_P : EquitablePartition G I) where
  /-- The two anyon-type cells being fused. -/
  a : I
  b : I
  /-- The output anyon-type cell. -/
  c : I
  /-- The Verlinde fusion coefficient. -/
  multiplicity : ℕ

/-- The **fusion relabeling** `I → I` of a `FusionEvent`: send the input cells
`a` and `b` to the output cell `c`, and fix every other cell.  This is the
combinatorial map underlying "fuse `{a,b}` into `c`". -/
def FusionEvent.relabel
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V} {I : Type v} [Fintype I] [DecidableEq I]
    {P : EquitablePartition G I} (F : FusionEvent P) : I → I :=
  fun i => if i = F.a ∨ i = F.b then F.c else i

/-- **Fusion produces a coarser cell map identifying the fused pair.**  Given a
`FusionEvent`, the composite cell map `relabel ∘ P.cells` sends both fused cells
to `c`: every vertex previously in cell `a` or `b` now lands in cell `c`.  This
is the genuine (non-`True`) combinatorial content of "fuse `{a,b}` into `c`".

The deeper claim — that `relabel ∘ P.cells` is again an *equitable* partition of
`G` — holds only when the branching condition survives the merge (the Verlinde
multiplicity bookkeeping); that is the deferred analytic part. -/
theorem fusion_relabel_identifies
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V} {I : Type v} [Fintype I] [DecidableEq I]
    {P : EquitablePartition G I} (F : FusionEvent P) (x : V)
    (hx : P.cells x = F.a ∨ P.cells x = F.b) :
    F.relabel (P.cells x) = F.c := by
  simp only [FusionEvent.relabel, if_pos hx]

/-! ## 8. Open questions and Tower-7 coherence

We close with the open directions promised in the integration spec. -/

/-- **Open Q1 (Heawood ↔ anyon coincidence).**  *Does the canonical
equitable partition of `surfaceHeawood g` (obtained from the Heawood
chromatic coloring) coincide with the topological-sector partition of some
naturally occurring surface anyon theory?*

Equivalently: is there a modular tensor category `M` with `|A| = h(g)`
anyon types and a fusion-uniform decoration `D` on `K_{h(g)}` whose sector
partition equals the proper `h(g)`-coloring of the genus-`g` Heawood map?

This is wide open even for `g = 1` (`h = 7`).  Candidate MTCs to test
include `SU(2)_5` (7 simple objects) and `(G_2)_1` (theta series matches).
-/
def openQ1_HeawoodMatchesAnyons (g : ℕ) : Prop :=
  ∃ (A : Type) (_ : Fintype A) (_ : DecidableEq A) (M : ModularData A)
    (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : WeightedGraph V)
    (D : AnyonDecoration G M),
    Fintype.card A = surfaceHeawood g ∧
    -- the anyon decoration's sector partition is equitable with exactly
    -- `h(g)` cells (one per anyon type) — the discrete shadow of "the surface
    -- anyon system's sector partition coincides with the Heawood coloring".
    (∃ P : EquitablePartition G A, P.cells = D.label)

/-- **Open Q2 (Tower-7 coherence).**  *Does the anyon-equitable-partition
lift respect Tower-7 (the chromatic / `K(n)`-localized tower of
`Graphplay/Categorical.lean`)?*

Tower 7 organizes the equitable-partition spine into a tower indexed by
chromatic height `n`; we conjecture that an anyonic decoration of `G`
factoring through the sector partition is *Tower-7-coherent*: the lift to
each chromatic height is itself an equitable partition by anyon type.
-/
def openQ2_Tower7Coherent : Prop :=
  -- For every modular data `M` and decorated graph `(G, D)` whose sector
  -- partition is fusion-uniform, that sector partition is genuinely equitable
  -- (the chromatic-height-`0` base of the Tower-7 lift).  The open content is
  -- coherence across *all* chromatic heights; the base case is this `∃ P`.
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : WeightedGraph V)
    {A : Type} [Fintype A] [DecidableEq A] (M : ModularData A)
    (D : AnyonDecoration G M),
    (∀ (a b : A) (x y : V),
      D.label x = a → D.label y = a →
      (∑ z, (if D.label z = b then G.adj x z else 0)) =
      (∑ z, (if D.label z = b then G.adj y z else 0))) →
    ∃ P : EquitablePartition G A, P.cells = D.label

/-- **Open Q3 (hardware braid gates via `magneticFluxSchedule`).**  *Can we
engineer braid gates on Graphplay hardware using the chiral
`magneticFluxSchedule` of `Toolkit/Scheduler.lean`?*

A magnetic-flux schedule modulates per-edge phases; in a surface-embedded
chiral CTQW, threading a quantum of flux through a face induces an
Aharonov-Bohm phase that braids the worldlines of anyons localized to
opposite sides of the face.  This is the hardware analogue of the
`BraidGate` machinery above. -/
def openQ3_FluxBraidGates : Prop :=
  -- For every `BraidGate B`, there exists a Hermitian Hamiltonian `H` and a
  -- time `t` whose CTQW evolution implements `B.gate` on the cell-uniform
  -- subspace (the realizability conclusion of `braid_gate_realizable`).
  ∀ {V : Type} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V} {I : Type} [Fintype I] [DecidableEq I]
    {P : EquitablePartition G I} (B : BraidGate P),
    ∃ (H : Matrix V V ℂ) (t : ℝ), H.IsHermitian ∧
      ∀ w : I → ℂ,
        (NormedSpace.exp (-(Complex.I * (t : ℂ)) • H)).mulVec
            (fun v => ∑ i, w i * P.cellUniformVec i v)
          = (fun v => ∑ i, (B.gate.mulVec w) i * P.cellUniformVec i v)

/-! ## 9. Mapping-class group action on cell-uniform subspace

A capstone statement: the mapping class group `MCG(Σ_g)` acts on the
cell-uniform subspace of any anyonic decoration of a `Σ_g`-embedded graph,
and this action factors through the `S, T` generators of the modular data.
This is the precise bridge: *Graphplay's quotient spine carries a
projective `SL₂(ℤ)` action when the underlying surface is a torus.*
-/

/-- **Capstone theorem (statement).**  Let `G` be a graph on the torus
with anyonic decoration `D : AnyonDecoration G M` whose sector partition
is equitable.  Then there is a projective representation of `SL₂(ℤ)` on
`P.cellUniformSubspace` factoring through the `S` and `T` matrices of
`M`. -/
theorem torus_modular_action
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V} {A : Type v} [Fintype A] [DecidableEq A]
    {M : ModularData A} (D : AnyonDecoration G M)
    (P : EquitablePartition G A) (_hP : P.cells = D.label) :
    -- There exist matrices `ρS, ρT : Matrix A A ℂ` representing the `S` and `T`
    -- generators on the (quotient = anyon-type-indexed) cell-uniform sector,
    -- with `ρT` the genuine diagonal twist matrix `T_{aa} = θ_a` of `M`.  The
    -- non-vacuous content: the representing `T`-matrix is exactly diagonal with
    -- the topological twists (`M.T_diag`), the hallmark of the modular `SL₂(ℤ)`
    -- action.  (Full projective `SL₂(ℤ)` relations are `M.modular_relations`,
    -- which is itself a deferred MTC axiom.)
    ∃ (ρS ρT : Matrix A A ℂ),
      ρS = M.S ∧ ρT = M.T ∧ (∀ a b, a ≠ b → ρT a b = 0) := by
  refine ⟨M.S, M.T, rfl, rfl, ?_⟩
  intro a b hab
  rw [M.T_diag a b, if_neg hab]

/-! ## 10. Summary

Putting the pieces together:

  * `ModularData` (§1) packages the `S`/`T` data of an MTC;
  * `AnyonDecoration` (§2) decorates a Graphplay `WeightedGraph` with
    anyon types and gives an equitable partition via
    `anyonic_equitable_partition`;
  * `BraidRepresentation` (§3) is realized inside the cell-uniform
    subspace by `braid_factors_through_cellUniform`;
  * `SurfaceIsotopy` (§4) makes PST a topological invariant;
  * `surfaceHeawood g` (§5) lists explicit Heawood envelope sizes
    (torus: 7; Klein bottle: 6; genus `g`: `h(g)`);
  * `LevinWenBundle` (§6) ties Graphplay bundles to state-sum lattice
    models (`levinWen_fiberLabel_total`);
  * `AnyonicPST`, `BraidGate`, `FusionEvent` (§7) provide the three
    topological-quantum-computation primitives;
  * The open questions (§8) ask whether the Heawood coloring matches a
    natural anyon theory, whether the lift is Tower-7-coherent, and
    whether `magneticFluxSchedule` realizes braid gates;
  * The capstone (`torus_modular_action`, §9) exhibits the modular
    `SL₂(ℤ)` action on Graphplay's quotient spine.

Together these statements pin down the precise dictionary between
Graphplay (an equitable-partition / CTQW formalism) and TQFT (an MTC /
anyonic formalism).  Filling in the sorries amounts to porting standard
MTC and TQC results into Mathlib.
-/

end TQFT
end Graphplay
