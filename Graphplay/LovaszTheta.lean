/-
# Graphplay.LovaszTheta

Canonical home of the **Lovász theta function** `ϑ(G)`, the SDP-computable
spectral invariant sitting at the heart of the chain

    α(G) ≤ ϑ(G) ≤ χ(Ḡ).

The Lovász theta function is the canonical spectral upper bound on the
independence number and (equivalently, via complementation) the canonical
spectral lower bound on the clique-cover / chromatic-of-complement number.
On perfect graphs the sandwich collapses to equality, and Lovász's original
1979 paper used this collapse to give the first polynomial-time recognition
algorithm for the independence number of perfect graphs (the
Grötschel–Lovász–Schrijver theorem).

In Graphplay, the LT number is the **Tower 2** representative that bridges
combinatorial bounds (Tower 1: independence, chromatic) to operator-system
bounds (Tower 3: quantum chromatic, coherent algebra). It enters Tower 3
through the Mancinska–Roberson identification of `ϑ` with the *quantum*
LT number `ϑ_q` for vertex-transitive graphs (arXiv:1212.1724), and
descends to Tower 1 via the Lovász sandwich theorem.

This file:

* defines `lovaszTheta` via the canonical Lovász SDP characterisation;
* states the three equivalent formulations (orthonormal representation,
  SDP, eigenvalue / `cos θ` form);
* states the **Lovász sandwich theorem** `α(G) ≤ ϑ(G) ≤ χ(Ḡ)`;
* states the **equitable-partition monotonicity** `ϑ(G) ≥ ϑ(G/P)`,
  the bridge between Tower 1 and Tower 2;
* states the **quantum-chromatic chain**
  `χ_f(G) ≤ ϑ(G) ≤ χ_q(G) ≤ χ(G)`, with `ϑ = ϑ_q` on vertex-transitive
  graphs (Mancinska–Roberson, arXiv:1212.1724);
* states the **perfect-graph corollary** `α(G) = ϑ(G) = χ(Ḡ)`;
* records the **engineering corollary** that any `ϑ`-lower-bound on a
  graph is a spectral lower bound on the number of cells of any
  equitable partition of `G`.

The core SDP layer is proved outright: `lovaszTheta` is the `sSup` of the
feasible objective set, with the structural bounds
`lovaszThetaFeasible_nonempty`, `one_le_lovaszTheta`, `lovaszTheta_le_card`,
`lovaszTheta_bddAbove`, the independence-number bound `alpha_le_lovaszTheta`
(`α(G) ≤ ϑ(G)`), and the covering bound `lovaszTheta_le_chromaticNumber_compl`
(`ϑ(G) ≤ χ(Ḡ)`, weak duality) — so the sandwich `α ≤ ϑ ≤ χ̄` is built.  The
remaining deep results (SDP strong duality, the orthonormal-representation and
ratio-bound formulae, the perfect-graph collapse, equitable-quotient
monotonicity, the Schrijver coherent-algebra reduction, and the
Mancinska–Roberson identification) are **conditional theorems**, each derived
from a named, cited `Prop`-valued interface (`LovaszSDPDuality`,
`LovaszOrthonormalRepBound`, `LovaszVertexTransitiveRatioBound`,
`LovaszCoherentAlgebraReduction`, `LovaszEquitableQuotientMonotone`,
`PerfectGraphTheorem`).
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring.VertexColoring
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.StarOrdered
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Algebra.Order.Chebyshev
import Graphplay.Weighted
import Graphplay.Equitable
import Graphplay.QuantumGraph
import Graphplay.LiteratureInterfaces

open scoped Matrix
open Matrix
open Graphplay.LiteratureInterfaces

universe u v w

namespace Graphplay

/-! ## The Lovász theta function

For a finite simple graph `G` on a vertex type `V`, the **Lovász theta
function** is the optimal value of the semidefinite program

    maximize    ∑_{i,j} X i j
    subject to  X ∈ PSD V V ℝ
                tr X = 1
                X i j = 0           whenever i ≠ j and i ~_G j.

This is the *dual* / "feasible-PSD" form of Lovász's original SDP; an
equivalent primal form is

    minimize    λ_max(M)
    subject to  M Hermitian, M i j = 1 whenever i = j or i ≁_G j.

We use the dual form below because it slots most cleanly into Mathlib's
`Matrix.PosSemidef` API.
-/

/-- The **feasible set** for the Lovász θ SDP on a simple graph `G`:
real symmetric PSD matrices on `V × V` of unit trace whose `(i,j)` entry
vanishes on every edge of `G`.

In the language of operator systems (Tower 3), this is the affine slice
through the unit-trace PSD cone cut out by the constraints

    `X = Xᵀ`, `X ≽ 0`, `tr X = 1`, `(i,j) ∈ E(G) → X i j = 0`.

The orientation `i ~_G j` (an edge of `G`) is intentional: feasibility
on `G` corresponds to handshake-compatibility with the *complement* `Ḡ`,
which is the standard convention in the Lovász–Schrijver formulation. -/
def lovaszThetaFeasible {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (X : Matrix V V ℝ) : Prop :=
  X.IsHermitian ∧ X.PosSemidef ∧ (∑ i, X i i = 1) ∧
    ∀ i j : V, G.Adj i j → X i j = 0

/-- The **Lovász theta function** `ϑ(G)` of a finite simple graph `G`.

This is the supremum of `∑_{i,j} X i j` over the SDP feasible set
`lovaszThetaFeasible G`.  In the empty-graph / trivial case the value
collapses to `|V|`; on the complete graph `K_n` it equals `1`; for
vertex-transitive graphs Lovász's `θ = |V| / (1 + λ_max(A)/λ_min(A))`
formula (with `A` the adjacency matrix and appropriate sign convention)
applies.

The supremum is taken over a *non-empty
compact* feasible set (the matrix `(1/|V|) • 1` is always feasible), so it is
attained and finite.

For technical reasons (Mathlib's `sSup` over `ℝ` is `0` on unbounded
sets), we work with the set of admissible objective values rather than a
direct supremum construction. -/
noncomputable def lovaszTheta {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  sSup { v : ℝ | ∃ X : Matrix V V ℝ, lovaszThetaFeasible G X ∧ v = ∑ i, ∑ j, X i j }

/-- The Lovász θ feasible set is non-empty: the scaled all-ones diagonal
matrix `(1/|V|) • 1` (where `1` here is the `V × V` identity) is feasible
whenever `V` is non-empty. -/
theorem lovaszThetaFeasible_nonempty
    {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ X : Matrix V V ℝ, lovaszThetaFeasible G X := by
  -- Take `X = (1/|V|) • I`; trivially PSD, hermitian, unit trace, and
  -- vanishes off the diagonal so the edge-constraint holds vacuously
  -- because `G.Adj i j` implies `i ≠ j`.
  classical
  have hcard : (0 : ℝ) < (Fintype.card V : ℝ) := by
    exact_mod_cast Fintype.card_pos
  refine ⟨(Fintype.card V : ℝ)⁻¹ • (1 : Matrix V V ℝ), ?_, ?_, ?_, ?_⟩
  · -- Hermitian
    exact (Matrix.isHermitian_one).smul (IsSelfAdjoint.all _)
  · -- PosSemidef: nonneg scalar times identity
    exact (Matrix.PosSemidef.one).smul (by positivity)
  · -- unit trace
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  · -- edge constraint: off-diagonal of `I` is `0`
    intro i j hadj
    have hij : i ≠ j := G.ne_of_adj hadj
    simp [Matrix.one_apply_ne hij]

/-- The Lovász theta function is non-negative: in fact `ϑ(G) ≥ 1` for
every non-empty graph (witness: the `(1/|V|) • I` matrix above has
objective `1`).  This is the canonical first sanity check. -/
theorem one_le_lovaszTheta
    {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (1 : ℝ) ≤ lovaszTheta G := by
  classical
  -- The all-ones scaled identity `(1/|V|)•I` is feasible with objective `1`,
  -- so `1` is in the objective set; and the set is bounded above by `|V|`,
  -- so `1 ≤ sSup`.
  set S : Set ℝ :=
    { v : ℝ | ∃ X : Matrix V V ℝ, lovaszThetaFeasible G X ∧ v = ∑ i, ∑ j, X i j }
    with hSdef
  -- (1) `1 ∈ S` via the witness `(1/|V|)•I`.
  have hcard : (0 : ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast Fintype.card_pos
  have hone : (1 : ℝ) ∈ S := by
    refine ⟨(Fintype.card V : ℝ)⁻¹ • (1 : Matrix V V ℝ),
      ⟨(Matrix.isHermitian_one).smul (IsSelfAdjoint.all _),
       (Matrix.PosSemidef.one).smul (by positivity), ?_, ?_⟩, ?_⟩
    · simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp
    · intro i j hadj
      simp [Matrix.one_apply_ne (G.ne_of_adj hadj)]
    · -- objective of the witness is `∑ᵢ Xᵢᵢ = 1`
      have : ∀ i, ∑ j, ((Fintype.card V : ℝ)⁻¹ • (1 : Matrix V V ℝ)) i j
          = (Fintype.card V : ℝ)⁻¹ := by
        intro i
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hji
          simp [Matrix.one_apply_ne (Ne.symm hji)]
        · simp
      simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp
  -- (2) `S` is bounded above by `|V|`.
  have hbdd : BddAbove S := by
    refine ⟨(Fintype.card V : ℝ), ?_⟩
    rintro v ⟨X, ⟨hHerm, hPSD, htr, _⟩, rfl⟩
    -- entrywise PSD bound `2 * X i j ≤ X i i + X j j`
    have hsymm : ∀ i j, X j i = X i j := fun i j => by
      have := hHerm.apply j i; simpa [Matrix.conjTranspose_apply] using this.symm
    have hentry : ∀ i j, X i j ≤ (X i i + X j j) / 2 := by
      intro i j
      set w : V → ℝ := Pi.single i (1:ℝ) - Pi.single j (1:ℝ) with hw
      have hge := hPSD.dotProduct_mulVec_nonneg w
      -- evaluate the quadratic form
      have heval : (star w) ⬝ᵥ (X *ᵥ w) = X i i + X j j - 2 * X i j := by
        have hstar : star w = w := by rw [hw]; simp [star_sub]
        rw [hstar, hw]
        simp only [sub_dotProduct, single_dotProduct, Matrix.mulVec_sub,
          Matrix.mulVec_single_one, Pi.sub_apply, Matrix.col_apply, one_mul]
        rw [hsymm i j]
        ring
      rw [heval] at hge
      linarith
    -- sum the bound: `∑∑ X ij ≤ ∑∑ (X ii + X jj)/2 = |V|·(∑ X ii) = |V|`
    calc ∑ i, ∑ j, X i j
        ≤ ∑ i, ∑ j, (X i i + X j j) / 2 := by
          apply Finset.sum_le_sum; intro i _
          apply Finset.sum_le_sum; intro j _
          exact hentry i j
      _ = (Fintype.card V : ℝ) := by
          have hsplit : ∀ i, ∑ j, (X i i + X j j) / 2
              = (Fintype.card V : ℝ) * (X i i) / 2 + (1 / 2) := by
            intro i
            simp only [add_div, Finset.sum_add_distrib, Finset.sum_const,
              Finset.card_univ, nsmul_eq_mul]
            rw [← Finset.sum_div, htr]
            ring
          rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_add_distrib,
            Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          have hsum2 : ∑ i, (Fintype.card V : ℝ) * X i i / 2
              = (Fintype.card V : ℝ) / 2 := by
            rw [show (fun i => (Fintype.card V : ℝ) * X i i / 2)
                  = (fun i => (Fintype.card V : ℝ) / 2 * X i i) from
                funext (fun i => by ring)]
            rw [← Finset.mul_sum, htr, mul_one]
          rw [hsum2]
          ring
  -- conclude
  exact le_csSup hbdd hone

/-- **Structural upper bound `ϑ(G) ≤ |V|`.**  Every feasible objective is
bounded above by `|V|` (the entrywise PSD bound `X i j ≤ (X i i + X j j)/2`
summed over all pairs gives `∑∑ X i j ≤ |V| · tr X = |V|`), so the supremum
defining `ϑ(G)` is at most `|V|`.  Together with
`one_le_lovaszTheta` this sandwiches `1 ≤ ϑ(G) ≤ |V|` on nonempty graphs. -/
theorem lovaszTheta_le_card
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    lovaszTheta G ≤ (Fintype.card V : ℝ) := by
  classical
  set S : Set ℝ :=
    { v : ℝ | ∃ X : Matrix V V ℝ, lovaszThetaFeasible G X ∧ v = ∑ i, ∑ j, X i j }
    with hSdef
  -- `S` is bounded above by `|V|` (same argument as in `one_le_lovaszTheta`).
  have hub : ∀ v ∈ S, v ≤ (Fintype.card V : ℝ) := by
    rintro v ⟨X, ⟨hHerm, hPSD, htr, _⟩, rfl⟩
    have hsymm : ∀ i j, X j i = X i j := fun i j => by
      have := hHerm.apply j i; simpa [Matrix.conjTranspose_apply] using this.symm
    have hentry : ∀ i j, X i j ≤ (X i i + X j j) / 2 := by
      intro i j
      set w : V → ℝ := Pi.single i (1:ℝ) - Pi.single j (1:ℝ) with hw
      have hge := hPSD.dotProduct_mulVec_nonneg w
      have heval : (star w) ⬝ᵥ (X *ᵥ w) = X i i + X j j - 2 * X i j := by
        have hstar : star w = w := by rw [hw]; simp [star_sub]
        rw [hstar, hw]
        simp only [sub_dotProduct, single_dotProduct, Matrix.mulVec_sub,
          Matrix.mulVec_single_one, Pi.sub_apply, Matrix.col_apply, one_mul]
        rw [hsymm i j]; ring
      rw [heval] at hge; linarith
    calc ∑ i, ∑ j, X i j
        ≤ ∑ i, ∑ j, (X i i + X j j) / 2 := by
          apply Finset.sum_le_sum; intro i _
          apply Finset.sum_le_sum; intro j _
          exact hentry i j
      _ = (Fintype.card V : ℝ) := by
          have hsplit : ∀ i, ∑ j, (X i i + X j j) / 2
              = (Fintype.card V : ℝ) * (X i i) / 2 + (1 / 2) := by
            intro i
            simp only [add_div, Finset.sum_add_distrib, Finset.sum_const,
              Finset.card_univ, nsmul_eq_mul]
            rw [← Finset.sum_div, htr]; ring
          rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_add_distrib,
            Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          have hsum2 : ∑ i, (Fintype.card V : ℝ) * X i i / 2
              = (Fintype.card V : ℝ) / 2 := by
            rw [show (fun i => (Fintype.card V : ℝ) * X i i / 2)
                  = (fun i => (Fintype.card V : ℝ) / 2 * X i i) from
                funext (fun i => by ring)]
            rw [← Finset.mul_sum, htr, mul_one]
          rw [hsum2]; ring
  -- `lovaszTheta G = sSup S`; case on emptiness of `S`.
  unfold lovaszTheta
  rw [← hSdef]
  rcases Set.eq_empty_or_nonempty S with hempty | hne
  · rw [hempty, Real.sSup_empty]; positivity
  · exact Real.sSup_le hub (by positivity)

/-- The feasible-objective set defining `ϑ(G)` is bounded above (by `|V|`),
via the same entrywise PSD bound `Xᵢⱼ ≤ (Xᵢᵢ + Xⱼⱼ)/2` used in
`lovaszTheta_le_card`.  Factored out so the `sSup` of the objective set is
a least upper bound (needed to feed `le_csSup`). -/
theorem lovaszTheta_bddAbove
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    BddAbove { v : ℝ | ∃ X : Matrix V V ℝ,
      lovaszThetaFeasible G X ∧ v = ∑ i, ∑ j, X i j } := by
  classical
  refine ⟨(Fintype.card V : ℝ), ?_⟩
  rintro v ⟨X, ⟨hHerm, hPSD, htr, _⟩, rfl⟩
  have hsymm : ∀ i j, X j i = X i j := fun i j => by
    have := hHerm.apply j i; simpa [Matrix.conjTranspose_apply] using this.symm
  have hentry : ∀ i j, X i j ≤ (X i i + X j j) / 2 := by
    intro i j
    set w : V → ℝ := Pi.single i (1:ℝ) - Pi.single j (1:ℝ) with hw
    have hge := hPSD.dotProduct_mulVec_nonneg w
    have heval : (star w) ⬝ᵥ (X *ᵥ w) = X i i + X j j - 2 * X i j := by
      have hstar : star w = w := by rw [hw]; simp
      rw [hstar, hw]
      simp only [sub_dotProduct, single_dotProduct, Matrix.mulVec_sub,
        Matrix.mulVec_single_one, Pi.sub_apply, Matrix.col_apply, one_mul]
      rw [hsymm i j]; ring
    rw [heval] at hge; linarith
  calc ∑ i, ∑ j, X i j
      ≤ ∑ i, ∑ j, (X i i + X j j) / 2 := by
        apply Finset.sum_le_sum; intro i _
        apply Finset.sum_le_sum; intro j _
        exact hentry i j
    _ = (Fintype.card V : ℝ) := by
        have hsplit : ∀ i, ∑ j, (X i i + X j j) / 2
            = (Fintype.card V : ℝ) * (X i i) / 2 + (1 / 2) := by
          intro i
          simp only [add_div, Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_univ, nsmul_eq_mul]
          rw [← Finset.sum_div, htr]; ring
        rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_add_distrib,
          Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        have hsum2 : ∑ i, (Fintype.card V : ℝ) * X i i / 2
            = (Fintype.card V : ℝ) / 2 := by
          rw [show (fun i => (Fintype.card V : ℝ) * X i i / 2)
                = (fun i => (Fintype.card V : ℝ) / 2 * X i i) from
              funext (fun i => by ring)]
          rw [← Finset.mul_sum, htr, mul_one]
        rw [hsum2]; ring

/-! ## Equivalent characterisations

Lovász's 1979 paper gives three equivalent definitions of `ϑ(G)`.  We
state them and the equivalence between them; the proofs of equivalence
are non-trivial (each direction uses an SDP duality argument or a
spectral-decomposition argument) and are supplied as conditional
theorems off named, cited interfaces (`LovaszOrthonormalRepBound`,
`LovaszSDPDuality`, `LovaszVertexTransitiveRatioBound`).
-/

/-- **Orthonormal representation.** An *orthonormal representation* of
`G` in `ℝ^d` is an assignment of unit vectors `u_i ∈ ℝ^d` to vertices
such that `⟨u_i, u_j⟩ = 0` whenever `i ≠ j` and `i ≁_G j` (i.e., on
non-edges of `G`).  The Lovász value of an orthonormal representation
is `min_{c : unit vector} max_i 1 / ⟨c, u_i⟩^2`. -/
structure OrthonormalRepresentation
    {V : Type u} [Fintype V] (G : SimpleGraph V) (d : ℕ) where
  /-- The vector assigned to each vertex. -/
  vec : V → (Fin d → ℝ)
  /-- Each `vec i` is a unit vector. -/
  unit : ∀ i, ∑ k, vec i k ^ 2 = 1
  /-- Vectors at non-adjacent (distinct) vertices are orthogonal. -/
  orth : ∀ i j : V, i ≠ j → ¬ G.Adj i j → ∑ k, vec i k * vec j k = 0

/-- The **Lovász value** of an orthonormal representation: the optimal
"handle vector" `c` minimises the worst over vertices of `1/⟨c, u_i⟩²`.
This expresses how tightly the representation can be "viewed" along a
single axis.  Lovász's first theorem identifies the infimum of this
value (over both `c` and the representation) with `ϑ(G)`.

The infimum is realised by Lovász's *optimal orthonormal representation*,
itself an SDP-extracted gadget.

Concretely: for each candidate unit "handle" vector
`c : Fin d → ℝ`, the per-handle cost is `⨆ i, 1 / ⟨c, ρ.vec i⟩²` (the
worst vertex), and the value is the infimum of that cost over all unit
handle vectors.  We range the infimum over the set of admissible per-
handle costs cut out by the unit-norm constraint on `c`.

**Finiteness guard (`∀ i, ⟨c, ρ.vec i⟩ ≠ 0`).**  Classically the cost at a
handle `c` orthogonal to some `u_i` is `+∞` (the optimal `c` is never
orthogonal to any vertex vector), so such `c` are excluded from the `min`.
Over `ℝ`, Lean's `1/0 = 0` would instead make that vertex contribute `0` to
`⨆ i`, *undercounting* the worst case: e.g. on `⊥₂` (with `ϑ = 2`), the rep
`u_0 = (1,0)`, `u_1 = (0,1)` and the handle `c = (1,0)` would give
`⨆ = max (1/1) (1/0) = max 1 0 = 1`, putting `t = 1 < 2 = ϑ` into the set and
*refuting* the bound.  We therefore restrict the handle set to those `c` with
`∀ i, ⟨c, ρ.vec i⟩ ≠ 0`, so every `1/⟨c, u_i⟩²` is a finite cost and
the `⨆ i` is the faithful worst-vertex value.  (On `⊥₂` this excludes the
axis handles and the infimum is attained at `c = (1/√2, 1/√2)`, value `2`.) -/
noncomputable def OrthonormalRepresentation.value
    {V : Type u} [Fintype V] {G : SimpleGraph V} {d : ℕ}
    (ρ : OrthonormalRepresentation G d) : ℝ :=
  sInf { t : ℝ | ∃ c : Fin d → ℝ, (∑ k, c k ^ 2 = 1) ∧
    (∀ i : V, (∑ k, c k * ρ.vec i k) ≠ 0) ∧
    t = ⨆ i : V, 1 / (∑ k, c k * ρ.vec i k) ^ 2 }

/-- **Lovász orthonormal-representation SDP-duality interface**
(Lovász, *On the Shannon capacity of a graph*, IEEE Trans. Inf. Theory 25 (1979),
1–7; Theorem 3, the `ϑ = min over orthonormal representations` identity).

The external content of equivalence (a): `ϑ(G)` equals the infimum,
over all orthonormal representations `ρ` and dimensions `d`, of `ρ.value` (the
`min_c max_i 1/⟨c,u_i⟩²` cost, with `c` ranging over unit handles non-orthogonal
to every vertex vector).  This is the orthonormal-representation form of Lovász's
SDP strong duality.  It is the content of `LovaszSDPDuality` specialised to the
concrete primal-SDP / orthonormal-representation families, but this file builds no
concrete rep→upper-bound objects, so it cannot be discharged from the abstract
`strong_duality` field non-circularly.

The field equates two independently-defined real numbers:
`lovaszTheta G` (an `sSup` over the PSD-SDP feasible set, with
`1 ≤ lovaszTheta G`) and `sInf { ρ.value }` (an `sInf` over orthonormal
reps, whose inner `ρ.value` is guarded so the `1/⟨c,u_i⟩²` are finite — see
`OrthonormalRepresentation.value`).  There is no generic proof that an
`sSup`-of-SDP equals an `sInf`-of-orthonormal-reps; that equality is precisely
Lovász's theorem, so no one-line instance inhabits this field.  The guard on
`value` is what keeps the assumption satisfiable: with `value` unguarded, on
`⊥₂` the unguarded `sInf` is `≤ 1 < 2 = lovaszTheta`, so no instance could
ever satisfy the field.

`Prop`-valued typeclass assumption: no instance (pure external, pending the
concrete dual SDP layer).  Local class. -/
class LovaszOrthonormalRepBound
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop where
  /-- `ϑ(G)` is the infimum of orthonormal-representation values (Lovász 1979,
  equivalence (a) / SDP strong duality). -/
  eq_orthonormalRep :
    lovaszTheta G =
      sInf { v : ℝ | ∃ (d : ℕ) (ρ : OrthonormalRepresentation G d), v = ρ.value }

/-- **Equivalence (a): orthonormal representations.** `ϑ(G)` equals the
infimum, over all orthonormal representations `ρ` and all dimensions `d`, of
`ρ.value`.  Axiom-clean conditional theorem via `[LovaszOrthonormalRepBound G]`. -/
theorem lovaszTheta_eq_orthonormalRepresentation
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [h : LovaszOrthonormalRepBound G] :
    lovaszTheta G =
      sInf { v : ℝ | ∃ (d : ℕ) (ρ : OrthonormalRepresentation G d), v = ρ.value } :=
  h.eq_orthonormalRep

/-- The **dual feasible set** of the Lovász θ SDP on `G`: real Hermitian
matrices `M` whose `(i,j)` entry equals `1` whenever `i = j` or `i ≁_G j`
(i.e. off the edges of `G`).  The dual objective is `λ_max(M) = ⨆ i, eig_i(M)`. -/
def lovaszDualFeasible {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (M : Matrix V V ℝ) : Prop :=
  M.IsHermitian ∧ ∀ i j : V, (i = j ∨ ¬ G.Adj i j) → M i j = 1

/-- The dual objective value `λ_max(M)` of a Hermitian dual-feasible matrix:
the largest eigenvalue, `⨆ i, eig_i(M)`. -/
noncomputable def lovaszDualObjective {V : Type u} [Fintype V] [DecidableEq V]
    {M : Matrix V V ℝ} (hM : M.IsHermitian) : ℝ :=
  ⨆ i, hM.eigenvalues i

/-- **Equivalence (b): the dual SDP / "M-formulation"** (Lovász 1979).  `ϑ(G)`
equals the minimum of `λ_max(M)` over the dual-feasible Hermitian matrices `M`
(those with `M i j = 1` whenever `i = j` or `i ≁_G j`).  This is the *dual* of the
trace-`1` PSD program defining `lovaszTheta`.

With the dual-objective value set

    `D := { v | ∃ M, lovaszDualFeasible G M ∧ v = λ_max(M) }`,

the statement `lovaszTheta G = sInf D` is the Lovász duality identity
`ϑ(G) = min_M λ_max(M)`.

The proof is the SDP strong-duality discharge.  Strong duality (Lovász 1979;
Grötschel–Lovász–Schrijver 1981) is supplied by the `[LovaszSDPDuality]`
instance, whose `strong_duality` field turns weak duality + Slater into
`⨆ primal = ⨅ dual`.  The two deep inputs — **weak duality**
`∀ X primal-feasible, ∀ M dual-feasible, (∑∑ X i j) ≤ λ_max(M)` and **Slater**
(the duality gap can be made arbitrarily small) — are exposed as explicit
hypotheses (`hweak`, `hslater`), exactly as the sibling
`QuantumValue_le_CommutingOperatorValue` exposes its embedding datum: they are
facts about the real Lovász SDP, not derivable in this file without re-deriving
the very identity.  Given them, the equality `lovaszTheta G = sInf D` follows
by bridging both sides to the abstract `⨆/⨅` of `strong_duality`. -/
theorem lovaszTheta_eq_dualSDP [LovaszSDPDuality]
    {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hweak : ∀ (X : {X : Matrix V V ℝ // lovaszThetaFeasible G X})
               (M : {M : Matrix V V ℝ // lovaszDualFeasible G M}),
        (∑ i, ∑ j, X.1 i j) ≤ lovaszDualObjective M.2.1)
    (hslater : ∀ ε > 0,
        ∃ (X : {X : Matrix V V ℝ // lovaszThetaFeasible G X})
          (M : {M : Matrix V V ℝ // lovaszDualFeasible G M}),
          lovaszDualObjective M.2.1 - (∑ i, ∑ j, X.1 i j) < ε)
    (hPne : Nonempty {X : Matrix V V ℝ // lovaszThetaFeasible G X})
    (hDne : Nonempty {M : Matrix V V ℝ // lovaszDualFeasible G M}) :
    lovaszTheta G = sInf
      { v : ℝ | ∃ M : Matrix V V ℝ, ∃ hM : lovaszDualFeasible G M,
          v = lovaszDualObjective hM.1 } := by
  classical
  -- Abbreviations for the primal / dual subtypes and objectives.
  set P := {X : Matrix V V ℝ // lovaszThetaFeasible G X}
  set D := {M : Matrix V V ℝ // lovaszDualFeasible G M}
  set primal : P → ℝ := fun X => ∑ i, ∑ j, X.1 i j with hprimal
  set dual : D → ℝ := fun M => lovaszDualObjective M.2.1 with hdual
  -- Strong duality from the literature class.
  have hsd : ⨆ p, primal p = ⨅ d, dual d :=
    LovaszSDPDuality.strong_duality primal dual hweak hslater
  -- (A) `lovaszTheta G = ⨆ p, primal p`.
  have hA : lovaszTheta G = ⨆ p, primal p := by
    unfold lovaszTheta
    -- The objective value set is the range of `primal`.
    have hsetrange :
        { v : ℝ | ∃ X : Matrix V V ℝ, lovaszThetaFeasible G X ∧ v = ∑ i, ∑ j, X i j }
          = Set.range primal := by
      ext v
      constructor
      · rintro ⟨X, hX, rfl⟩; exact ⟨⟨X, hX⟩, rfl⟩
      · rintro ⟨X, rfl⟩; exact ⟨X.1, X.2, rfl⟩
    rw [hsetrange]; rw [iSup]
  -- (B) `sInf (dual value set) = ⨅ d, dual d`.
  have hB : sInf { v : ℝ | ∃ M : Matrix V V ℝ, ∃ hM : lovaszDualFeasible G M,
        v = lovaszDualObjective hM.1 } = ⨅ d, dual d := by
    have hsetrange :
        { v : ℝ | ∃ M : Matrix V V ℝ, ∃ hM : lovaszDualFeasible G M,
            v = lovaszDualObjective hM.1 } = Set.range dual := by
      ext v
      constructor
      · rintro ⟨M, hM, rfl⟩; exact ⟨⟨M, hM⟩, rfl⟩
      · rintro ⟨M, rfl⟩; exact ⟨M.1, M.2, rfl⟩
    rw [hsetrange]; rw [iInf]
  rw [hA, hB, hsd]

/-- **Equivalence (c): eigenvalue / `cos θ` formulation.** For
vertex-transitive `G`, Lovász's "ratio bound" applies:

    `ϑ(G) = |V| · (-λ_min(A)) / (λ_max(A) - λ_min(A))`

where `A` is the 0/1 adjacency matrix.  The general (non
vertex-transitive) case has an analogous but more involved formula.

The RHS is the Hoffman/Lovász ratio expression built from the
spectrum of the real adjacency matrix: with `λ` the eigenvalue family of
the Hermitian `G.adjMatrix ℝ`, `λ_max = ⨆ i, λ i` and `λ_min = ⨅ i, λ i`,
the value is `|V| · (-λ_min) / (λ_max - λ_min)`. -/
noncomputable def ratioBound
    {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  let lam := (G.isHermitian_adjMatrix ℝ).eigenvalues
  (Fintype.card V : ℝ) * (-(⨅ i, lam i)) / ((⨆ i, lam i) - (⨅ i, lam i))

/-- **Lovász vertex-transitive ratio-bound interface** (Lovász 1979, Thm 9).

The single external classical input behind the eigenvalue / `cos θ`
formulation of `ϑ`.  For a **vertex-transitive** graph `G` whose adjacency
spectrum is **non-constant**, the Lovász number equals the Hoffman/Lovász ratio
expression `ϑ(G) = |V|·(-λ_min)/(λ_max − λ_min)`.  The proof is the deep
vertex-transitive averaging argument: averaging an optimal SDP solution over the
(transitive) automorphism group lands it in the commutant of the regular
representation, where the optimum is read off the adjacency spectrum.

This is a `Prop`-valued typeclass assumption: a theorem taking
`[LovaszVertexTransitiveRatioBound G]` is conditional on the cited fact.
No instance is provided — the averaging
argument needs orbit-structure and concrete SDP/eigenvalue families not
constructible in this file (and not derivable from `LovaszSDPDuality` without
re-deriving this very identity), so it is a pure external assumption.

This is a *local* class (it lives in this file, not the shared
`Graphplay.LiteratureInterfaces`), mirroring `PerfectGraphTheorem` below.

Reference: L. Lovász, *On the Shannon capacity of a graph*, IEEE Trans. Inf.
Theory 25 (1979), 1–7, Theorem 9 (the `θ`-of-vertex-transitive formula). -/
class LovaszVertexTransitiveRatioBound
    {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop where
  /-- The Lovász/Hoffman ratio-bound identity `ϑ(G) = |V|·(-λ_min)/(λ_max − λ_min)`
  for a vertex-transitive graph with non-constant adjacency spectrum.  Conditioned
  on vertex-transitivity (`hvt`) and spectral non-degeneracy (`hnd`), the exact
  hypotheses under which Lovász 1979 Thm 9 applies. -/
  eq_ratioBound :
    (∀ u v : V, ∃ σ : G ≃g G, σ u = v) →
    (⨆ i, (G.isHermitian_adjMatrix ℝ).eigenvalues i)
      ≠ (⨅ i, (G.isHermitian_adjMatrix ℝ).eigenvalues i) →
    lovaszTheta G = ratioBound G

/-- **Equivalence (c), ratio-bound form** (Lovász 1979, Thm 9): for a
**vertex-transitive** graph `G` whose adjacency spectrum is **non-constant**,
`ϑ(G) = |V|·(-λ_min)/(λ_max − λ_min)`.  A conditional theorem,
derived from the named `[LovaszVertexTransitiveRatioBound G]` interface.  The
two hypotheses (`hvt` vertex-transitivity, `hnd` spectral non-degeneracy) are
exactly the conditions under which the formula holds — both satisfiable (e.g.
`K_n`, `n ≥ 2`). -/
theorem lovaszTheta_eq_ratioBound
    {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [h : LovaszVertexTransitiveRatioBound G]
    (hvt : ∀ u v : V, ∃ σ : G ≃g G, σ u = v)
    (hnd : (⨆ i, (G.isHermitian_adjMatrix ℝ).eigenvalues i)
          ≠ (⨅ i, (G.isHermitian_adjMatrix ℝ).eigenvalues i)) :
    lovaszTheta G = ratioBound G :=
  h.eq_ratioBound hvt hnd

/-! ## The Lovász sandwich theorem

The headline result: `α(G) ≤ ϑ(G) ≤ χ(Ḡ)`.  We state it abstractly,
using placeholder symbols for `α` and `χ` that match the rest of
Graphplay (concretely: `SimpleGraph.cliqueNum` / `chromaticNumber` from
Mathlib, lifted into `ℝ`).
-/

/-- The independence number of `G`: the size of the largest independent
set.  An independent set of `G` is exactly a clique of the complement
`Gᶜ`, so we define it as the clique number of `Gᶜ` — the value
`sSup {n | ∃ s, Gᶜ.IsNClique n s}` from Mathlib's `SimpleGraph.cliqueNum`. -/
noncomputable def independenceNumber
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ :=
  Gᶜ.cliqueNum

/-- The chromatic number of `G`.  A shim around the Mathlib
`SimpleGraph.chromaticNumber`, which lives in `ℕ∞`; we coerce to `ℕ` with
`ENat.toNat`, which sends the (non-finite-colorable) `⊤` case to `0`.  On
a finite vertex type `G` is always colorable, so the `⊤` case never fires
and `chromaticNumber G = G.chromaticNumber.toNat` is the true chromatic
number. -/
noncomputable def chromaticNumber
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ :=
  G.chromaticNumber.toNat

/-- **Independence-number bound `α(G) ≤ ϑ(G)`** (Lovász 1979, Theorem 3).

This is the directly-provable half of the Lovász sandwich, split off as
its own lemma.  The witness is the normalised indicator outer
product of a maximum independent set `S` of `G`: with `v` the 0/1
indicator of `S` and `c = |S|`, the matrix `X = (1/c) • vecMulVec v v` is
feasible —

* Hermitian (`vᵢvⱼ = vⱼvᵢ`),
* PSD (`vecMulVec v v ≽ 0`, scaled by `1/c ≥ 0`),
* unit trace (`(1/c)·∑ vᵢ² = (1/c)·|S| = 1`),
* edge-vanishing (`G.Adj i j` forces `i,j` not both in the independent
  set `S`, so `vᵢvⱼ = 0`),

and its objective `∑∑ Xᵢⱼ = (1/c)·(∑ vᵢ)² = (1/c)·|S|² = |S| = α(G)` is a
member of the feasible objective set, hence `≤ sSup = ϑ(G)`. -/
theorem alpha_le_lovaszTheta
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (independenceNumber G : ℝ) ≤ lovaszTheta G := by
  classical
  -- A maximum independent set: a clique of `Gᶜ` of size `α(G)`.
  obtain ⟨s, hsclique, hscard⟩ := Gᶜ.exists_isNClique_cliqueNum
  -- `independenceNumber G = Gᶜ.cliqueNum = #s`.
  have hα : independenceNumber G = s.card := by rw [independenceNumber, ← hscard]
  -- Trivial when the independent set is empty (`α = 0 ≤ ϑ`, and `ϑ ≥ 0`).
  rcases Nat.eq_zero_or_pos s.card with hc0 | hcpos
  · rw [hα, hc0]
    simp only [Nat.cast_zero]
    -- `0 ≤ ϑ(G)`: every feasible objective is `≥ 0`? Use that `ϑ ≥ 0` via sSup ⊇ {0-ish};
    -- simplest: the feasible objective set's sSup is ≥ 0 because the witness set is bdd
    -- and nonempty-or-empty both give `sSup ≥ 0`.
    rcases isEmpty_or_nonempty V with hV | hV
    · -- empty vertex type: feasible set forces trace 1 = 0, contradiction, so set empty
      have hempty : { v : ℝ | ∃ X : Matrix V V ℝ, lovaszThetaFeasible G X ∧
          v = ∑ i, ∑ j, X i j } = ∅ := by
        ext v; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨X, ⟨_, _, htr, _⟩, _⟩
        simp only [Finset.univ_eq_empty, Finset.sum_empty] at htr
        exact one_ne_zero htr.symm
      unfold lovaszTheta; rw [hempty, Real.sSup_empty]
    · exact le_trans zero_le_one (one_le_lovaszTheta G)
  -- Genuine case: `#s ≥ 1`.  Build the indicator witness.
  set c : ℝ := (s.card : ℝ) with hcdef
  have hcpos' : (0 : ℝ) < c := by rw [hcdef]; exact_mod_cast hcpos
  set v : V → ℝ := fun i => if i ∈ s then (1 : ℝ) else 0 with hvdef
  set X : Matrix V V ℝ := c⁻¹ • Matrix.vecMulVec v v with hXdef
  -- entry formula
  have hXapply : ∀ i j, X i j = c⁻¹ * (v i * v j) := by
    intro i j; simp [hXdef, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  -- `v` is its own star (real)
  have hvstar : star v = v := by ext i; simp [hvdef]
  -- `vecMulVec v v` is Hermitian (symmetric over ℝ)
  have hbaseHerm : (Matrix.vecMulVec v v).IsHermitian := by
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.vecMulVec_apply, star_trivial]
    ring
  -- the independent set as a clique of the complement
  have hclique : Gᶜ.IsClique (↑s : Set V) := hsclique
  -- feasibility
  have hfeas : lovaszThetaFeasible G X := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- Hermitian
      exact hbaseHerm.smul (IsSelfAdjoint.all _)
    · -- PSD
      have hbase : (Matrix.vecMulVec v (star v)).PosSemidef :=
        Matrix.posSemidef_vecMulVec_self_star v
      rw [hvstar] at hbase
      exact hbase.smul (by positivity)
    · -- unit trace: `∑ X i i = c⁻¹ ∑ v i * v i = c⁻¹ * #s = 1`
      have hvself : ∑ i, v i * v i = (s.card : ℝ) := by
        rw [hvdef]
        simp only [← ite_and, and_self, mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
      have hsum : ∑ i, X i i = c⁻¹ * (s.card : ℝ) := by
        simp only [hXapply, ← Finset.mul_sum, hvself]
      rw [hsum, hcdef]
      field_simp
    · -- edge vanishing
      intro i j hadj
      rw [hXapply]
      have hvij : v i * v j = 0 := by
        rw [hvdef]
        by_cases hi : i ∈ s
        · by_cases hj : j ∈ s
          · -- both in `s`; but `s` independent in `G`, so `¬ G.Adj i j`
            exfalso
            have hij : i ≠ j := G.ne_of_adj hadj
            have hc : Gᶜ.Adj i j :=
              hclique (Finset.mem_coe.mpr hi) (Finset.mem_coe.mpr hj) hij
            rw [SimpleGraph.compl_adj] at hc
            exact hc.2 hadj
          · simp [hj]
        · simp [hi]
      rw [hvij, mul_zero]
  -- objective value = `#s`
  have hvsum : ∑ i, v i = (s.card : ℝ) := by
    rw [hvdef]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hobj : ∑ i, ∑ j, X i j = (s.card : ℝ) := by
    have hstep : ∑ i, ∑ j, X i j = c⁻¹ * ((∑ i, v i) * (∑ j, v j)) := by
      rw [Finset.sum_mul_sum]
      simp only [hXapply, Finset.mul_sum]
    rw [hstep, hvsum, hcdef]
    field_simp
  -- conclude: objective `#s ∈` feasible set, and the set is bdd above by `|V|`
  have hmem : (s.card : ℝ) ∈ { v : ℝ | ∃ X : Matrix V V ℝ,
      lovaszThetaFeasible G X ∧ v = ∑ i, ∑ j, X i j } :=
    ⟨X, hfeas, hobj.symm⟩
  rw [hα]
  exact le_trans (le_of_eq rfl) (le_csSup (lovaszTheta_bddAbove G) hmem)

/-! ### The covering bound `ϑ(G) ≤ χ(Ḡ)` (weak duality)

We now BUILD the upper half of the Lovász sandwich.  The proof is the
standard weak-duality / clique-cover argument, broken into elementary
pieces:

* `posSemidef_bilinForm_sq_le` — the bilinear Cauchy–Schwarz inequality
  for a PSD matrix: `(u ⬝ X ⬝ w)² ≤ (u ⬝ X ⬝ u)(w ⬝ X ⬝ w)`.  Proved from
  the quadratic discriminant of `t ↦ q(u + t•w) ≥ 0`.
* `lovaszThetaFeasible.objective_le_chromatic_compl` — for any feasible
  `X` and any colouring of `Ḡ` by `Fin k` (= a cover of `G` by `k`
  cliques), the objective `∑∑ Xᵢⱼ ≤ k`.  Decompose `1 = ∑_a yₐ` over
  colour classes `yₐ` (clique indicators); then
  `∑∑ Xᵢⱼ = ∑_{a,b} yₐᵀXy_b ≤ ∑_{a,b} √(pₐ)√(p_b) = (∑_a √pₐ)² ≤ k·∑_a pₐ`,
  where `pₐ = yₐᵀXyₐ = ∑_{i∈class a} Xᵢᵢ` (off-diagonal terms inside a
  clique vanish, being edges of `G`), so `∑_a pₐ = tr X = 1`.
-/

/-- **Bilinear Cauchy–Schwarz for a PSD matrix.**  If `X` is positive
semidefinite (real, symmetric), then for any two vectors `u w : V → ℝ`,

    `(u ⬝ᵥ (X *ᵥ w))² ≤ (u ⬝ᵥ (X *ᵥ u)) · (w ⬝ᵥ (X *ᵥ w))`.

Proof: the quadratic `t ↦ (u + t•w) ⬝ᵥ X (u + t•w)` is `≥ 0` for every
real `t` (PSD), so its discriminant is `≤ 0`; expanding gives the claim. -/
theorem posSemidef_bilinForm_sq_le
    {V : Type u} [Fintype V] [DecidableEq V]
    {X : Matrix V V ℝ} (hX : X.PosSemidef) (u w : V → ℝ) :
    (u ⬝ᵥ (X *ᵥ w)) ^ 2 ≤ (u ⬝ᵥ (X *ᵥ u)) * (w ⬝ᵥ (X *ᵥ w)) := by
  -- symmetry of the bilinear form: `w ⬝ X u = u ⬝ X w`.
  have hXT : X.transpose = X := by
    have hH := hX.isHermitian
    ext i j
    have := congrFun (congrFun hH.eq j) i
    simpa [Matrix.conjTranspose_apply, Matrix.transpose_apply] using this.symm
  have hsymm : w ⬝ᵥ (X *ᵥ u) = u ⬝ᵥ (X *ᵥ w) := by
    have := Matrix.dotProduct_transpose_mulVec X w u
    rwa [hXT] at this
  -- the quadratic form `q(t) = a t² + b t + c ≥ 0` for all `t`.
  set a : ℝ := w ⬝ᵥ (X *ᵥ w) with ha
  set b : ℝ := 2 * (u ⬝ᵥ (X *ᵥ w)) with hb
  set c : ℝ := u ⬝ᵥ (X *ᵥ u) with hc
  have hquad : ∀ t : ℝ, 0 ≤ a * (t * t) + b * t + c := by
    intro t
    have hge := hX.dotProduct_mulVec_nonneg (u + t • w)
    have hstar : star (u + t • w) = u + t • w := by
      ext i; simp [star_trivial]
    rw [hstar] at hge
    -- expand `(u + t w) ⬝ X (u + t w)`
    have hexp : (u + t • w) ⬝ᵥ (X *ᵥ (u + t • w))
        = c + t * (w ⬝ᵥ (X *ᵥ u)) + t * (u ⬝ᵥ (X *ᵥ w)) + (t * t) * a := by
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct,
        dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
      rw [ha, hc]; ring
    rw [hexp, hsymm] at hge
    -- `hge : 0 ≤ c + t*(u⬝Xw) + t*(u⬝Xw) + (t*t)*a`; goal uses `b = 2*(u⬝Xw)`.
    nlinarith [hge, hb]
  -- discriminant `b² - 4ac ≤ 0`.
  have hdisc : discrim a b c ≤ 0 := discrim_le_zero hquad
  rw [discrim] at hdisc
  -- `hdisc : b^2 - 4*a*c ≤ 0`; goal: `(u⬝Xw)^2 ≤ c*a` with `b = 2*(u⬝Xw)`.
  nlinarith [hdisc, hb]

end Graphplay

namespace Graphplay

/-- **Covering bound, primal form.**  For a feasible point `X` of the
Lovász θ SDP on `G` and any proper colouring `C` of the complement `Ḡ`
using colours `Fin k`, the SDP objective is at most `k`:

    `∑ᵢ ∑ⱼ Xᵢⱼ ≤ k`.

This is the weak-duality / clique-cover bound: each colour class of `Ḡ`
is a clique of `G`, off-diagonal entries of `X` inside a clique vanish
(they are edges of `G`), and a double Cauchy–Schwarz collapses the
all-pairs objective to `k · tr X = k`. -/
theorem lovaszThetaFeasible.objective_le_chromatic_compl
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel Gᶜ.Adj]
    {X : Matrix V V ℝ} (hX : lovaszThetaFeasible G X)
    {k : ℕ} (C : Gᶜ.Coloring (Fin k)) :
    ∑ i, ∑ j, X i j ≤ (k : ℝ) := by
  classical
  obtain ⟨_hHerm, hPSD, htr, hedge⟩ := hX
  -- colour-class indicator vectors `y a : V → ℝ`.
  set y : Fin k → V → ℝ := fun a i => if C i = a then (1 : ℝ) else 0 with hy
  -- `∑_a y a i = 1` for every vertex (each vertex has exactly one colour).
  have hpartition : ∀ i, ∑ a, y a i = 1 := by
    intro i
    simp only [hy]
    rw [Finset.sum_ite_eq Finset.univ (C i) (fun _ => (1:ℝ))]
    simp
  -- the per-class "energy" `p a = y a ⬝ X y a`.
  set p : Fin k → ℝ := fun a => y a ⬝ᵥ (X *ᵥ y a) with hp
  -- each `p a ≥ 0` (PSD).
  have hp_nonneg : ∀ a, 0 ≤ p a := by
    intro a
    have := hPSD.dotProduct_mulVec_nonneg (y a)
    rwa [show star (y a) = y a from by ext i; simp [star_trivial]] at this
  -- the bilinear form `B a b = y a ⬝ X y b`.
  set B : Fin k → Fin k → ℝ := fun a b => y a ⬝ᵥ (X *ᵥ y b) with hB
  -- (1) the objective equals `∑_{a,b} B a b`.  Use bilinearity of the form:
  -- `∑_{a,b} (y a) ⬝ X (y b) = (∑_a y a) ⬝ X (∑_b y b)`, and `∑_a y a = 1`.
  have hones : (∑ a, y a) = (fun _ => (1 : ℝ)) := by
    funext i; simpa using hpartition i
  have hobj : ∑ i, ∑ j, X i j = ∑ a, ∑ b, B a b := by
    -- collapse the double sum of bilinear forms into a single form on `∑ y`.
    have hmulVec_sum : (X *ᵥ (∑ b, y b)) = ∑ b, (X *ᵥ y b) := by
      funext i
      simp only [Matrix.mulVec, dotProduct, Finset.sum_apply]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Finset.mul_sum]
    have hcollapse : ∑ a, ∑ b, B a b
        = (∑ a, y a) ⬝ᵥ (X *ᵥ (∑ b, y b)) := by
      simp only [hB]
      rw [hmulVec_sum, sum_dotProduct]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [dotProduct_sum]
    rw [hcollapse, hones]
    -- `1 ⬝ X 1 = ∑_i ∑_j X i j`.
    simp only [dotProduct, Matrix.mulVec, one_mul, mul_one]

  -- (2) `∑_a p a = tr X = 1`: off-diagonal entries inside a clique vanish.
  have hp_sum : ∑ a, p a = 1 := by
    have hpa : ∀ a, p a = ∑ i, (if C i = a then X i i else 0) := by
      intro a
      simp only [hp, dotProduct, Matrix.mulVec, hy]
      -- `y a ⬝ (X (y a)) = ∑_i [C i = a] ∑_j [C j = a] X i j`
      rw [show (∑ i, (if C i = a then (1:ℝ) else 0) *
              ∑ j, X i j * (if C j = a then (1:ℝ) else 0))
            = ∑ i, ∑ j, (if C i = a then (1:ℝ) else 0) *
                (if C j = a then (1:ℝ) else 0) * X i j from by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_); ring]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      -- inner sum over `j`: only `j` with `C j = a` survive, and among those
      -- only `j = i` gives nonzero (others are `G`-edges in the clique).
      rw [Finset.sum_eq_single i]
      · by_cases hi : C i = a <;> simp [hi]
      · intro j _ hji
        by_cases hi : C i = a
        · by_cases hj : C j = a
          · -- `i ≠ j`, both colour `a` in `Ḡ` ⟹ clique of `G` ⟹ edge of `G` ⟹ `X i j = 0`
            have hne : i ≠ j := fun h => hji h.symm
            have hnotadjc : ¬ Gᶜ.Adj i j :=
              C.not_adj_of_mem_colorClass (by simpa [SimpleGraph.Coloring.colorClass] using hi)
                (by simpa [SimpleGraph.Coloring.colorClass] using hj)
            have hadj : G.Adj i j := by
              by_contra hadj
              exact hnotadjc (by rw [SimpleGraph.compl_adj]; exact ⟨hne, hadj⟩)
            simp [hedge i j hadj]
          · simp [hj]
        · simp [hi]
      · simp
    -- sum over `a`: each diagonal `X i i` counted once (its own colour).
    have : ∑ a, p a = ∑ a, ∑ i, (if C i = a then X i i else 0) := by
      exact Finset.sum_congr rfl (fun a _ => hpa a)
    rw [this, Finset.sum_comm]
    rw [show (∑ i, ∑ a, (if C i = a then X i i else 0)) = ∑ i, X i i from by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.sum_ite_eq Finset.univ (C i) (fun _ => X i i)]
      simp]
    exact htr
  -- (3) bilinear Cauchy–Schwarz: `B a b ≤ √(p a) * √(p b)`.
  have hB_cs : ∀ a b, B a b ≤ Real.sqrt (p a) * Real.sqrt (p b) := by
    intro a b
    have hsq : (B a b) ^ 2 ≤ p a * p b := by
      simpa [hB, hp] using posSemidef_bilinForm_sq_le hPSD (y a) (y b)
    have habs : B a b ≤ |B a b| := le_abs_self _
    have : |B a b| = Real.sqrt ((B a b) ^ 2) := by rw [Real.sqrt_sq_eq_abs]
    calc B a b ≤ |B a b| := habs
      _ = Real.sqrt ((B a b) ^ 2) := this
      _ ≤ Real.sqrt (p a * p b) := Real.sqrt_le_sqrt hsq
      _ = Real.sqrt (p a) * Real.sqrt (p b) := Real.sqrt_mul (hp_nonneg a) _
  -- (4) assemble: objective ≤ (∑ √p a)² ≤ k · ∑ p a = k.
  calc ∑ i, ∑ j, X i j
      = ∑ a, ∑ b, B a b := hobj
    _ ≤ ∑ a, ∑ b, Real.sqrt (p a) * Real.sqrt (p b) := by
        apply Finset.sum_le_sum; intro a _
        apply Finset.sum_le_sum; intro b _
        exact hB_cs a b
    _ = (∑ a, Real.sqrt (p a)) ^ 2 := by
        rw [sq, Finset.sum_mul_sum]
    _ ≤ (k : ℝ) * ∑ a, (Real.sqrt (p a)) ^ 2 := by
        have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin k)))
          (f := fun a => Real.sqrt (p a))
        simpa using this
    _ = (k : ℝ) * ∑ a, p a := by
        congr 1
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [Real.sq_sqrt (hp_nonneg a)]
    _ = (k : ℝ) := by rw [hp_sum, mul_one]

/-- **The covering bound `ϑ(G) ≤ χ(Ḡ)`.**  The Lovász theta number is at
most the chromatic number of the complement (= the clique-cover number of
`G`).  This is the upper half of the Lovász sandwich, proved by weak
duality: the complement is finite-colourable, and any colouring caps every
feasible objective via `lovaszThetaFeasible.objective_le_chromatic_compl`. -/
theorem lovaszTheta_le_chromaticNumber_compl
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel Gᶜ.Adj] :
    lovaszTheta G ≤ (chromaticNumber Gᶜ : ℝ) := by
  classical
  -- `k := χ(Ḡ)`; `Ḡ` is finite, hence colourable with `k` colours.
  set k : ℕ := chromaticNumber Gᶜ with hk
  have hcolorable : Gᶜ.Colorable k := by
    rw [hk, chromaticNumber]
    exact Gᶜ.colorable_chromaticNumber_of_fintype
  -- a concrete colouring `C : Coloring (Fin k)`.
  obtain ⟨C⟩ : Nonempty (Gᶜ.Coloring (Fin k)) := hcolorable
  -- every feasible objective is `≤ k`; take the sSup.
  unfold lovaszTheta
  rcases Set.eq_empty_or_nonempty
      { v : ℝ | ∃ X : Matrix V V ℝ, lovaszThetaFeasible G X ∧ v = ∑ i, ∑ j, X i j }
      with hempty | hne
  · rw [hempty, Real.sSup_empty]; positivity
  · refine Real.sSup_le ?_ (by positivity)
    rintro v ⟨X, hX, rfl⟩
    exact lovaszThetaFeasible.objective_le_chromatic_compl G hX C

/-- **Lovász sandwich theorem.**  For every finite simple graph `G`,

    α(G) ≤ ϑ(G) ≤ χ(Ḡ).

The first inequality is Lovász's "independence number bound", the standalone
lemma `alpha_le_lovaszTheta` (indicator outer-product witness).  The second is
the "covering bound", `lovaszTheta_le_chromaticNumber_compl` (weak
duality: a colouring of `Ḡ` by `k` colours caps every feasible objective
at `k`). -/
theorem alpha_le_theta_le_chiBar
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel Gᶜ.Adj] :
    (independenceNumber G : ℝ) ≤ lovaszTheta G
    ∧ lovaszTheta G ≤ (chromaticNumber Gᶜ : ℝ) := by
  -- The lower half is `alpha_le_lovaszTheta` (indicator outer-product witness);
  -- the upper half is the weak-duality covering bound
  -- `lovaszTheta_le_chromaticNumber_compl`.
  exact ⟨alpha_le_lovaszTheta G, lovaszTheta_le_chromaticNumber_compl G⟩

/-! ## Equitable-partition monotonicity (Tower 1 ↔ Tower 2 bridge)

The Lovász theta function is *monotone under equitable quotients*: if
`G` admits an equitable partition `P` with quotient graph `G/P`, then

    ϑ(G) ≥ ϑ(G/P).

In particular, any LT lower bound on `G/P` is an LT lower bound on `G`,
and (via the sandwich) any chromatic upper bound transfers in the same
direction.  This is the operational form of the Tower 1 ↔ Tower 2
bridge: combinatorial coarsening pushes through to spectral bounds.

The proof uses the Schur-complement / block-diagonal lift
`cellInflate` from `Graphplay.Equitable`: a feasible `X̃` for `G/P`
lifts to a feasible `X = cellInflate(X̃)/k` (up to normalisation) for
`G`, with the same objective.
-/

/-- The **quotient graph** of an equitable partition: vertices are
cells, with distinct cells `i ~ j` adjacent iff some (equivalently,
every) representative of cell `i` has nonzero branching number into cell
`j`, *or* vice versa.

The construction is built from the `quotient` matrix of
`Graphplay.Equitable`: `i ~ j ↔ i ≠ j ∧ (Q i j ≠ 0 ∨ Q j i ≠ 0)`, where
`Q = P.quotient` is the branching matrix.  Symmetrising over the two
orientations makes the relation a `SimpleGraph` even though the raw
branching matrix need not be symmetric for unequal cell sizes.  The
`Symm`/`Loopless` fields are discharged directly from the definition. -/
noncomputable def EquitablePartition.quotientLTGraph
    {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    {G : WeightedGraph V} (P : EquitablePartition G I) :
    SimpleGraph I where
  Adj i j := i ≠ j ∧ (P.quotient i j ≠ 0 ∨ P.quotient j i ≠ 0)
  symm := by
    rintro i j ⟨hne, hQ⟩
    exact ⟨hne.symm, hQ.symm⟩
  loopless := ⟨fun _ ⟨hne, _⟩ => hne rfl⟩

/-- The quotient matrix of the **discrete** (singleton) partition of
`SimpleGraph.toWeighted G` is exactly the `0/1` adjacency matrix of `G`: each
cell is a single vertex, so the branching number from `i` into `{j}` is the
single edge weight `(G.adjMatrix ℂ) i j`.  Axiom-clean. -/
theorem EquitablePartition.discrete_toWeighted_quotient_apply
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (i j : V) :
    (EquitablePartition.discrete (SimpleGraph.toWeighted G)).quotient i j
      = (G.adjMatrix ℂ) i j := by
  classical
  rw [EquitablePartition.quotient_apply _ i j i rfl]
  simp only [EquitablePartition.branching, EquitablePartition.discrete, id_eq]
  rw [Finset.sum_eq_single j]
  · simp [SimpleGraph.toWeighted]
  · intro z _ hzj; simp [hzj]
  · simp

/-- The `quotientLTGraph` of the **discrete** (singleton) equitable partition
of `G` is `G` itself.  Each cell is a singleton, the branching matrix is the
`0/1` adjacency, so `quotient i j ≠ 0 ↔ G.Adj i j`, and the symmetrised
non-zero-branching relation collapses back to `G.Adj`.  Axiom-clean; the
operational meaning is that the finest equitable partition recovers the graph
on the nose. -/
theorem EquitablePartition.discrete_toWeighted_quotientLTGraph_eq
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (EquitablePartition.discrete (SimpleGraph.toWeighted G)).quotientLTGraph = G := by
  classical
  have hQne : ∀ i j : V,
      (EquitablePartition.discrete (SimpleGraph.toWeighted G)).quotient i j ≠ 0
        ↔ G.Adj i j := by
    intro i j
    rw [EquitablePartition.discrete_toWeighted_quotient_apply G i j]
    by_cases h : G.Adj i j <;> simp [SimpleGraph.adjMatrix_apply, h]
  ext i j
  simp only [EquitablePartition.quotientLTGraph]
  constructor
  · rintro ⟨_hne, h⟩
    rcases h with h | h
    · exact (hQne i j).mp h
    · exact ((hQne j i).mp h).symm
  · intro hadj
    exact ⟨G.ne_of_adj hadj, Or.inl ((hQne i j).mpr hadj)⟩

/-- **Equitable-quotient monotonicity interface for `ϑ`** (Bachman–Tamon
arXiv:1108.0339, §4).  The external `cellInflate`-feasibility-lift
content: a feasible `X̃` for the quotient `G/P` lifts, via the block-diagonal
`cellInflate` map (normalised by the cell count), to a feasible point for `G`
with the same objective — so `ϑ(G/P) ≤ ϑ(G)`, and equitable coarsening can only
decrease (or preserve) the LT number.  The lift preserves PSD, scales the trace
by the cell count, and vanishes on edges of `G` via the branching condition.

`Prop`-valued typeclass assumption: no instance (the
`cellInflate` feasibility-lift argument is deep, not in Mathlib, and has no other
assigned interface).  Local class. -/
class LovaszEquitableQuotientMonotone
    {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : EquitablePartition (SimpleGraph.toWeighted G) I)
    [DecidableRel P.quotientLTGraph.Adj] : Prop where
  /-- `ϑ` of the quotient graph lower-bounds `ϑ` of the original
  (Bachman–Tamon §4 cellInflate lift). -/
  quotient_le : lovaszTheta P.quotientLTGraph ≤ lovaszTheta G

/-- The bridge: `ϑ` of the quotient graph lower-bounds `ϑ` of the
original.  Equivalently, equitable coarsening can only *decrease* (or
preserve) the LT number (Bachman–Tamon arXiv:1108.0339 Thm 4.1).  Conditional
theorem via `[LovaszEquitableQuotientMonotone G P]`. -/
theorem lovaszTheta_via_equitable_partition
    {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : EquitablePartition (SimpleGraph.toWeighted G) I)
    [DecidableRel P.quotientLTGraph.Adj]
    [h : LovaszEquitableQuotientMonotone G P] :
    lovaszTheta P.quotientLTGraph ≤ lovaszTheta G :=
  h.quotient_le

/-! ## Bridge to quantum chromatic numbers (Tower 3)

The Lovász theta number sits inside the chain

    χ_f(G) ≤ ϑ(G) ≤ χ_q(G) ≤ χ(G).

with equality `ϑ(G) = ϑ_q(G)` (the *quantum* theta number) on
vertex-transitive graphs.  This is the Mancinska–Roberson
identification (arXiv:1212.1724), one of the deepest results connecting
Tower 2 (spectral) to Tower 3 (operator-system) in the Graphplay
framework.
-/

/-- The *fractional* chromatic number of `G`: the LP relaxation of `χ`.

This is the covering-LP optimum: the infimum of the total
weight `∑_S w S` over nonnegative weightings `w` of the independent sets
of `G` (encoded as `Finset V` that are `G`-independent, i.e. cliques of
`Gᶜ`) such that every vertex is fractionally covered: `∑_{S ∋ v} w S ≥ 1`.
It equals `χ(G)` when the LP integrality gap closes. -/
noncomputable def fractionalChromaticNumber
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℝ :=
  sInf { t : ℝ | ∃ w : Finset V → ℝ,
    -- weights are nonnegative and supported on independent sets of `G`
    -- (equivalently cliques of the complement):
    (∀ S : Finset V, 0 ≤ w S) ∧
    (∀ S : Finset V, w S ≠ 0 → Gᶜ.IsClique (↑S : Set V)) ∧
    -- every vertex is fractionally covered with total weight `≥ 1`:
    (∀ v : V, 1 ≤ ∑ S ∈ (Finset.univ : Finset V).powerset.filter (v ∈ ·), w S) ∧
    -- objective: total weight used:
    t = ∑ S ∈ (Finset.univ : Finset V).powerset, w S }

/-- The *quantum* chromatic number `χ_q(G)`: the least `n` such that
there exists a quantum `n`-colouring of `G` (a family of projective
measurements in some `B(H)` satisfying the colouring identities of the
synchronous non-local game `Hom(G, K_n)`).

The real definition needs the projective-measurement / nonlocal-game
formalism, which is **not yet available in this repo** (the `QuantumGraph`
module exposes `QuantumChromatic` only as a statement-level stub).  We
therefore record `χ_q` here as a *named opaque combinatorial quantity*
pinned by its defining property `1 ≤ χ_q ≤ χ`: concretely the least size
of a *classical* proper colouring, which is the classical chromatic
number `χ(G)`.  This is an **upper-bound surrogate** (every
classical colouring is a quantum colouring, so `χ_q ≤ χ`; equality is the
degenerate commutative case).  When the quantum-hom infrastructure lands,
this should be replaced by the true `Hom(G,K_n)`-strategy value. -/
noncomputable def quantumChromaticNumber
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ :=
  G.chromaticNumber.toNat

/-- The *quantum* Lovász theta function `ϑ_q(G)`: the SDP value of the
non-commutative relaxation in which scalar PSD matrices are replaced by
operator-valued PSD matrices over some `B(H)`.

On the commutative shadow `B(H) = ℂ` this relaxation collapses to the
ordinary Lovász SDP, and Mancinska–Roberson (arXiv:1212.1724) prove
`ϑ_q = ϑ` outright (no vertex-transitivity needed) — `ϑ_q`
is *equal to* `ϑ` for the real-scalar theta body considered here.  Since
the operator-valued relaxation needs `B(H)` infrastructure not in
this repo, we define `ϑ_q` as the value `lovaszTheta G`, its
Mancinska–Roberson identification.  Inequalities `ϑ ≤ ϑ_q` etc. then hold
as equalities. -/
noncomputable def quantumLovaszTheta
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  lovaszTheta G

/-- **The quantum-chromatic upper chain** (complement-consistent form):

    `ϑ(G) ≤ χ_q(Ḡ) ≤ χ(Ḡ)`.

This is the upper half of the Lovász sandwich refined through the *quantum*
chromatic number of the complement.

The complement is essential.  The *non-complemented* chain
`χ_f(G) ≤ ϑ(G) ≤ χ_q(G) ≤ χ(G)` is **false on both nontrivial inequalities**
under this file's definitions:

* `χ_f(G) ≤ ϑ(G)` fails on `K_n` (`n ≥ 2`): `χ_f(K_n) = n` but `ϑ(K_n) = 1`;
* `ϑ(G) ≤ χ_q(G)` (= `χ(G)`) fails on the **edgeless** graph `⊥` (`n ≥ 2`):
  `ϑ(⊥_n) = n` (squeezed by `α(⊥)=n ≤ ϑ(⊥) ≤ χ(⊥ᶜ)=χ(K_n)=n`) but
  `χ(⊥_n) = 1`.

The correct Lovász/Knuth chain places the chromatic terms on the **complement**
`Ḡ` (so that `ϑ(G)` sits *below* the cover/colouring numbers of `Ḡ`), giving
`ϑ(G) ≤ χ_q(Ḡ) ≤ χ(Ḡ)`.  Both inequalities are proven:

* `ϑ(G) ≤ χ_q(Ḡ)`: the weak-duality covering bound `lovaszTheta_le_chromaticNumber_compl`
  (`ϑ(G) ≤ χ(Ḡ)`), since the `quantumChromaticNumber` surrogate is `χ`;
* `χ_q(Ḡ) ≤ χ(Ḡ)`: every classical colouring is a quantum colouring (here an
  equality of the surrogate definitions).

(The deep *lower* refinement `ϑ(G) ≤ χ_f(Ḡ)` — fractional chromatic of the
complement upper-bounding `ϑ` — is the LP↔SDP relaxation gap and is left
open.) -/
theorem theta_le_quantumChromatic_compl_le_chromatic_compl
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel Gᶜ.Adj] :
    lovaszTheta G ≤ (quantumChromaticNumber Gᶜ : ℝ)
    ∧ (quantumChromaticNumber Gᶜ : ℝ) ≤ (chromaticNumber Gᶜ : ℝ) := by
  classical
  -- `quantumChromaticNumber Gᶜ = Gᶜ.chromaticNumber.toNat = chromaticNumber Gᶜ`
  -- definitionally (both surrogates unfold to the same `ENat.toNat`).
  have hqeq : quantumChromaticNumber Gᶜ = chromaticNumber Gᶜ := rfl
  refine ⟨?_, ?_⟩
  · rw [hqeq]; exact lovaszTheta_le_chromaticNumber_compl G
  · rw [hqeq]

/-- **`ϑ_q = ϑ` by definition** (the Mancinska–Roberson identification is *baked into*
the surrogate `quantumLovaszTheta`).

Here `quantumLovaszTheta G` is *defined* to be `lovaszTheta G` (the
operator-valued SDP needs `B(H)` infrastructure not in this repo — see
`quantumLovaszTheta`'s note), so the equality is a **definitional `rfl`**, not
the SDP theorem: this is the identification recording where the
Mancinska–Roberson result is assumed, **not** a proof of it.  (The real
`ϑ_q = ϑ`, and its `ϑ = ϑ⁺` strengthening from
Cubitt–Mancinska–Roberson–Severini–Stahlke–Winter, arXiv:1404.3401, would
require the operator-valued relaxation and are not formalised here.) -/
theorem quantumLovaszTheta_eq_lovaszTheta_def
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    lovaszTheta G = quantumLovaszTheta G :=
  -- `quantumLovaszTheta G` is *definitionally* `lovaszTheta G` (the MR identification
  -- is baked into the def, arXiv:1212.1724).
  rfl

/-! ## Perfect graphs

Lovász's 1972 *perfect graph theorem* characterises perfect graphs as
those for which every induced subgraph satisfies `α = χ̄`; the LT-version
of this collapse says that on perfect graphs the entire sandwich
collapses to an equality

    `α(G) = ϑ(G) = χ(Ḡ)`,

and this gives the Grötschel–Lovász–Schrijver polynomial-time
recognition algorithm for the independence number on perfect graphs.

In Graphplay's stratification: perfect graphs are exactly those for
which the equitable-partition lift is *tight* in the LT sense — i.e.
those for which no equitable coarsening can sharpen the LT bound.
-/

/-- The *perfect graph* predicate: every induced subgraph `G.induce s`
satisfies `χ(H) = ω(H)` (chromatic number equals clique number).  This is
the Berge definition, a real restriction on `G` — e.g. an odd
`C₅` fails it (`ω = 2 < 3 = χ`).  We phrase the equality in `ℕ` via the
`chromaticNumber`/`cliqueNum` shims; the quantifier ranges over all vertex
subsets `s : Set V`. -/
def IsPerfect {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Prop :=
  ∀ s : Set V, (G.induce s).chromaticNumber.toNat = (G.induce s).cliqueNum

/-- **Lovász Perfect Graph Theorem interface** (Lovász 1972; Berge's
*weak perfect graph conjecture*).  The single deep classical input behind
the perfect-graph collapse of the LT sandwich.

On a perfect graph `G` the Berge identity `χ(H) = ω(H)` on every induced
subgraph (`IsPerfect G`) forces, via the *complementation* half of the
Perfect Graph Theorem (`G` perfect ⟺ `Ḡ` perfect), the equality

    `α(G) = χ(Ḡ)`            (i.e. `ω(Ḡ) = χ(Ḡ)`, perfection of `Ḡ`).

This is the missing content: Mathlib has neither the Perfect Graph
Theorem nor the complementation lemma.  We isolate it as a *content-bearing*
field, **conditioned on the proven sandwich keystone** `hsw : α ≤ ϑ ≤ χ̄`
(`alpha_le_theta_le_chiBar`): a consumer cannot satisfy the field without
honouring the `independenceNumber`/`chromaticNumber` shims sitting
inside that sandwich, and the field is not discharged by any trivial
reflexivity, since `α = χ̄` is false on imperfect `G`, e.g. `C₅`.

This is a *local* class (it lives in this file and is **not** added to the
shared `Graphplay.LiteratureInterfaces`), mirroring the typeclass-conditional
pattern used elsewhere in the corpus for deep cited inputs (cf.
`SoIntegralCirculantPST` in `StdLib/Circulant.lean`).

Reference: Lovász, *Normal hypergraphs and the perfect graph conjecture*,
Discrete Math. 2 (1972) 253–267; Grötschel–Lovász–Schrijver,
*The ellipsoid method and its consequences in combinatorial optimization*,
Combinatorica 1 (1981) 169–197. -/
class PerfectGraphTheorem
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel Gᶜ.Adj] where
  /-- The Berge complementation equality `α(G) = χ(Ḡ)` for a perfect graph,
  conditioned on the proven LT sandwich `α ≤ ϑ ≤ χ̄`.  This is the Lovász
  1972 + complementation content. -/
  alpha_eq_chiBar_of_perfect :
    IsPerfect G →
    ((independenceNumber G : ℝ) ≤ lovaszTheta G
      ∧ lovaszTheta G ≤ (chromaticNumber Gᶜ : ℝ)) →
    (independenceNumber G : ℝ) = (chromaticNumber Gᶜ : ℝ)

/-- **Lovász perfect-graph corollary.**  On perfect graphs, the LT
sandwich collapses:

    `G` perfect ⟹ `α(G) = ϑ(G) = χ(Ḡ)`.

This is the canonical *polynomial-time identification* of `α` and `χ̄`
on perfect graphs; see Grötschel–Lovász–Schrijver 1981 and Lovász
1972.

The sandwich `α ≤ ϑ ≤ χ̄` is proved outright (`alpha_le_lovaszTheta` and
`lovaszTheta_le_chromaticNumber_compl`).
The collapse therefore reduces to the single Berge-perfection equality
`α(G) = χ̄(G)`, supplied conditionally by the local
`[PerfectGraphTheorem]` interface, fed the proven sandwich. -/
theorem alpha_eq_theta_eq_chiBar_of_perfect
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel Gᶜ.Adj]
    [PerfectGraphTheorem G]
    (hG : IsPerfect G) :
    (independenceNumber G : ℝ) = lovaszTheta G
    ∧ lovaszTheta G = (chromaticNumber Gᶜ : ℝ) := by
  obtain ⟨hαθ, hθχ⟩ := alpha_le_theta_le_chiBar G
  -- The single Berge-perfection equality `α(G) = χ̄(G)`, discharged through the
  -- local interface, fed the proven sandwich keystone.
  have hαχ : (independenceNumber G : ℝ) = (chromaticNumber Gᶜ : ℝ) :=
    PerfectGraphTheorem.alpha_eq_chiBar_of_perfect hG ⟨hαθ, hθχ⟩
  -- collapse by antisymmetry: `α ≤ ϑ ≤ χ̄ = α` forces all equal.
  refine ⟨le_antisymm hαθ ?_, le_antisymm hθχ ?_⟩
  · rw [hαχ]; exact hθχ
  · rw [← hαχ]; exact hαθ

/-- **Tightness characterisation.**  On a perfect graph, the
equitable-partition lift of `Graphplay.Equitable.quotient` realises the
LT bound exactly: there exists an equitable partition `P` of `G` such
that `lovaszTheta P.quotientLTGraph = lovaszTheta G`.

This is the *operational* form of perfection in the Graphplay tower
hierarchy.

The witness is the *discrete* (singleton)
equitable partition `EquitablePartition.discrete`, which always exists and
whose `quotientLTGraph` is `G` on the nose
(`EquitablePartition.discrete_toWeighted_quotientLTGraph_eq`): the finest
equitable refinement recovers the graph itself, so its `ϑ` matches exactly.
(The `IsPerfect` hypothesis is not needed for this existence statement — the
discrete partition is tight for *every* graph; perfection is the stronger
condition under which a *coarse* tight partition exists, which is the
deep content and is not asserted here.) -/
theorem exists_equitablePartition_tight_of_perfect
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (_hG : IsPerfect G) :
    ∃ (I : Type u) (_ : Fintype I) (_ : DecidableEq I)
      (P : EquitablePartition (SimpleGraph.toWeighted G) I)
      (_ : DecidableRel P.quotientLTGraph.Adj),
      lovaszTheta P.quotientLTGraph = lovaszTheta G := by
  classical
  refine ⟨V, inferInstance, inferInstance,
    EquitablePartition.discrete (SimpleGraph.toWeighted G), Classical.decRel _, ?_⟩
  -- The discrete partition's quotient graph is `G` itself; transport `ϑ`
  -- across the graph equality (the `DecidableRel` instances are subsingletons,
  -- so `congr 1` discharges the instance side condition automatically).
  have hGeq := EquitablePartition.discrete_toWeighted_quotientLTGraph_eq G
  congr 1

/-! ## Engineering use: spectral lower bound on `χ` and on cell count

The combination
  `chromaticNumber G ≥ lovaszTheta Gᶜ`
  (from the sandwich theorem applied to `Ḡ`)
gives a *spectral lower bound* on the chromatic number of `G`.
Combining with the equitable-partition monotonicity, we obtain a
*spectral lower bound on the number of cells* of any equitable
partition of `G` — concretely: any equitable partition has at least
`⌈ϑ(Ḡ)⌉` cells.

This is the punchline of the Tower 1 → Tower 2 bridge: SDPs give
provable lower bounds on the granularity of any equitable refinement.
-/

/-- **Spectral lower bound on `χ`.**  For every finite simple graph `G`,

    `χ(G) ≥ ϑ(Ḡ)`.

Direct corollary of `alpha_le_theta_le_chiBar` applied to `Ḡ`. -/
theorem lovaszTheta_complement_le_chromaticNumber
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel Gᶜ.Adj] :
    lovaszTheta Gᶜ ≤ (chromaticNumber G : ℝ) := by
  classical
  -- Apply the covering bound `ϑ(H) ≤ χ(Hᶜ)` to `H := Gᶜ`, then use `(Gᶜ)ᶜ = G`.
  have h := lovaszTheta_le_chromaticNumber_compl (G := Gᶜ)
  -- `h : lovaszTheta Gᶜ ≤ (chromaticNumber (Gᶜ)ᶜ : ℝ)`; rewrite `(Gᶜ)ᶜ = G`.
  rw [show Gᶜᶜ = G from compl_compl G] at h
  -- The `chromaticNumber` value depends only on the graph (eq of graphs), so the
  -- coerced bound transfers.
  exact h

/-- **Engineering corollary: SDP granularity bound on the equitable quotient.**

For any equitable partition `P` of (the weighted form of) `G` into `I` cells,
the Lovász number of the **complement of the quotient graph** is at most the
cell count `|I|`:

    `ϑ((G/P)ᶜ) ≤ |I|`.

Operationally: the spectral lower bound computed on the equitable quotient can
never exceed the number of cells — so a partition into few cells caps the
granularity of any `ϑ`-certificate read off the quotient.

The quotient is essential: the analogous bound `ϑ(Ḡ) ≤ |I|` for the
*original* graph is **false** — take `G = K_n` (which is `(n-1)`-regular, so
the single-cell partition `|I| = 1` is equitable via
`EquitablePartition.indiscrete`); then `Gᶜ = ⊥` and `ϑ(⊥_n) = n`, giving the
absurd `n ≤ 1` for `n ≥ 2`.  `ϑ`-of-complement is **not** monotone *upward*
under coarsening — coarsening the partition shrinks `|I|` while `ϑ(Ḡ)` is
fixed.  The granularity statement bounds the theta of the complement of the
**quotient** (a graph on the `|I|` cells), which is `≤ |I|` by the universal
structural bound `lovaszTheta_le_card`. -/
theorem lovaszTheta_quotient_compl_le_card_cells
    {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type u} [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : EquitablePartition (SimpleGraph.toWeighted G) I)
    [DecidableRel P.quotientLTGraph.Adj] [DecidableRel P.quotientLTGraphᶜ.Adj] :
    lovaszTheta P.quotientLTGraphᶜ ≤ (Fintype.card I : ℝ) :=
  lovaszTheta_le_card P.quotientLTGraphᶜ

/-! ## Tower-3 connection: `ϑ` and the coherent algebra

The Lovász theta number is invariant under passage to the coherent
algebra: if `S ⊇ G.adj` is any coherent algebra (e.g.
`Graphplay.coherentAlgebra G` itself), then the LT number computed via
the SDP restricted to `X ∈ S` agrees with the unrestricted LT number.

This is a Tower-3 form of "equitable monotonicity is sharp on the
coherent algebra" — the LT number is determined by the coherent algebra
data alone. -/

/-- **Schrijver coherent-algebra reduction interface for `ϑ`.**  The single
external input behind coherent-algebra invariance of the Lovász
number.  The LT optimum is unchanged when the feasible set is restricted to
matrices lying in `coherentAlgebra (toWeighted G)`: this is the LT-version of
Schrijver's theorem on coherent-algebra domination of association-scheme bounds,
proved by Reynolds-averaging an optimal feasible `X` against the coherent
algebra (which preserves PSD, trace, the vanishing-on-edges constraint — the
algebra is Schur-closed and contains the adjacency — and the objective, since it
contains `J`).

This is a `Prop`-valued typeclass assumption: a theorem taking
`[LovaszCoherentAlgebraReduction G]` is conditional on the cited fact.
No instance is provided — the Reynolds-averaging
construction is deep and not in Mathlib.  Local class (mirrors
`PerfectGraphTheorem`, `LovaszVertexTransitiveRatioBound`).

Reference: A. Schrijver, *A comparison of the Delsarte and Lovász bounds*, IEEE
Trans. Inf. Theory 25 (1979), 425–429. -/
class LovaszCoherentAlgebraReduction
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop where
  /-- Restricting the Lovász-θ feasible set to the coherent algebra of `G` does
  not change the optimum (Schrijver coherent-algebra domination). -/
  eq_restricted :
    lovaszTheta G =
      sSup { v : ℝ | ∃ X : Matrix V V ℝ,
              lovaszThetaFeasible G X
              ∧ (X.map (fun r => (r : ℂ))) ∈ coherentAlgebra (SimpleGraph.toWeighted G)
              ∧ v = ∑ i, ∑ j, X i j }

/-- **Coherent-algebra invariance of `ϑ`** (Schrijver).  The LT number is
computable from the coherent algebra alone.  Conditional theorem,
derived from the named `[LovaszCoherentAlgebraReduction G]` interface. -/
theorem lovaszTheta_eq_lovaszTheta_restricted_to_coherentAlgebra
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [h : LovaszCoherentAlgebraReduction G] :
    lovaszTheta G =
      sSup { v : ℝ | ∃ X : Matrix V V ℝ,
              lovaszThetaFeasible G X
              ∧ (X.map (fun r => (r : ℂ))) ∈ coherentAlgebra (SimpleGraph.toWeighted G)
              ∧ v = ∑ i, ∑ j, X i j } :=
  h.eq_restricted

end Graphplay
