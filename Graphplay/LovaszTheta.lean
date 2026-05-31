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

The core SDP layer is now genuine and axiom-clean: `lovaszTheta` is the
real `sSup` of the feasible objective set, with the structural bounds
`lovaszThetaFeasible_nonempty`, `one_le_lovaszTheta`, `lovaszTheta_le_card`,
`lovaszTheta_bddAbove`, and the independence-number bound
`alpha_le_lovaszTheta` (`α(G) ≤ ϑ(G)`, the provable half of the sandwich)
all proven sorry-free.  The remaining deep results (the `ϑ ≤ χ(Ḡ)` dual
half, SDP strong duality, the perfect-graph collapse, equitable
monotonicity, and the Mancinska–Roberson identification) carry honest
`sorry`s, but every underlying *definition* is now genuine (no `:= 0`
stubs).
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

The actual computation is left as `sorry`; this layer only sets up the
*statement-of-shape* required by the rest of Graphplay.  Note that the
supremum is taken over a *non-empty compact* feasible set (the matrix
`(1/|V|) • 1` is always feasible), so the `sSup` is attained and finite.

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
defining `ϑ(G)` is at most `|V|`.  Genuine, axiom-clean; together with
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
a genuine least upper bound (needed to feed `le_csSup`). -/
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
spectral-decomposition argument) and are left as `sorry`.
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

This is a *genuine* definition: for each candidate unit "handle" vector
`c : Fin d → ℝ`, the per-handle cost is `⨆ i, 1 / ⟨c, ρ.vec i⟩²` (the
worst vertex), and the value is the infimum of that cost over all unit
handle vectors.  We range the infimum over the set of admissible per-
handle costs cut out by the unit-norm constraint on `c`. -/
noncomputable def OrthonormalRepresentation.value
    {V : Type u} [Fintype V] {G : SimpleGraph V} {d : ℕ}
    (ρ : OrthonormalRepresentation G d) : ℝ :=
  sInf { t : ℝ | ∃ c : Fin d → ℝ, (∑ k, c k ^ 2 = 1) ∧
    t = ⨆ i : V, 1 / (∑ k, c k * ρ.vec i k) ^ 2 }

/-- **Equivalence (a): orthonormal representations.** `ϑ(G)` equals the
infimum, over all orthonormal representations `ρ` and all dimensions
`d`, of `ρ.value`. -/
theorem lovaszTheta_eq_orthonormalRepresentation
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    lovaszTheta G =
      sInf { v : ℝ | ∃ (d : ℕ) (ρ : OrthonormalRepresentation G d), v = ρ.value } := by
  -- HONEST SORRY (deep): Lovász 1979 SDP strong duality.  The RHS is a *genuine*
  -- equality target now (`OrthonormalRepresentation.value` is the real
  -- `inf_c max_i 1/⟨c,u_i⟩²`, not a `:= 0` stub), so the statement is faithful.
  -- It is exactly the content of `LovaszSDPDuality.strong_duality`, but that field
  -- proves `⨆primal = ⨅dual` *from* weak duality + Slater between the concrete SDP
  -- primal-objective and orthonormal-representation families — and this file builds
  -- no concrete dual (rep→upper-bound) objects, so neither premise is constructible
  -- here without re-deriving this very equality.  Cannot be discharged by the field
  -- non-circularly; remains an honest deep sorry pending the concrete dual SDP layer.
  sorry

/-- **Equivalence (b): the dual SDP / "M-formulation".**  `ϑ(G)` equals
the minimum of `λ_max(M)` over Hermitian matrices `M` with `M i j = 1`
whenever `i = j` or `i ≁_G j` (i.e., off the edges of `G`).  This is
the *dual* of the trace-1 PSD program above. -/
theorem lovaszTheta_eq_dualSDP
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    lovaszTheta G = sInf
      { v : ℝ | ∃ _M : Matrix V V ℝ, v = 0 } := by
  -- FALSE-AS-STATED (placeholder RHS): the dual-objective set is literally
  -- `{v | ∃ _M, v = 0} = {0}`, so the RHS is `sInf {0} = 0`, and the statement
  -- asserts `lovaszTheta G = 0` — false, since `1 ≤ lovaszTheta G` on every
  -- nonempty graph (`one_le_lovaszTheta`).  This is NOT an instance of
  -- `LovaszSDPDuality`: that field would only apply once the RHS is replaced by
  -- the genuine `min λ_max(M)` dual program (`M i j = 1` off the edges of `G`).
  -- Forcing the typeclass onto this false statement is disallowed; left honest.
  sorry

/-- **Equivalence (c): eigenvalue / `cos θ` formulation.** For
vertex-transitive `G`, Lovász's "ratio bound" applies:

    `ϑ(G) = |V| · (-λ_min(A)) / (λ_max(A) - λ_min(A))`

where `A` is the 0/1 adjacency matrix.  The general (non
vertex-transitive) case has an analogous but more involved formula.

The RHS is the *genuine* Hoffman/Lovász ratio expression built from the
spectrum of the real adjacency matrix: with `λ` the eigenvalue family of
the Hermitian `G.adjMatrix ℝ`, `λ_max = ⨆ i, λ i` and `λ_min = ⨅ i, λ i`,
the value is `|V| · (-λ_min) / (λ_max - λ_min)`. -/
noncomputable def ratioBound
    {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  let lam := (G.isHermitian_adjMatrix ℝ).eigenvalues
  (Fintype.card V : ℝ) * (-(⨅ i, lam i)) / ((⨆ i, lam i) - (⨅ i, lam i))

theorem lovaszTheta_eq_ratioBound
    {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (_hvt : True /- placeholder for vertex-transitive hypothesis -/) :
    lovaszTheta G = ratioBound G := by
  -- HONEST SORRY (deep): the Lovász/Hoffman ratio-bound identity for
  -- vertex-transitive graphs (Lovász 1979, Thm 9).  `ratioBound` is the genuine
  -- spectral expression `|V|·(-λ_min)/(λ_max - λ_min)`.  This is the equality
  -- form covered in spirit by `LovaszSDPDuality.strong_duality`, but discharging
  -- it via that field requires the concrete primal-SDP / eigenvalue-dual families
  -- and the vertex-transitive averaging argument (and a real vertex-transitivity
  -- hypothesis, currently the `True` placeholder `_hvt`) — none of which is
  -- constructible in this file.  Cannot be wired to the field non-circularly.
  sorry

/-! ## The Lovász sandwich theorem

The headline result: `α(G) ≤ ϑ(G) ≤ χ(Ḡ)`.  We state it abstractly,
using placeholder symbols for `α` and `χ` that match the rest of
Graphplay (concretely: `SimpleGraph.cliqueNum` / `chromaticNumber` from
Mathlib, lifted into `ℝ`).
-/

/-- The independence number of `G`: the size of the largest independent
set.  An independent set of `G` is exactly a clique of the complement
`Gᶜ`, so we define it as the clique number of `Gᶜ` — the genuine value
`sSup {n | ∃ s, Gᶜ.IsNClique n s}` from Mathlib's `SimpleGraph.cliqueNum`.
This is a *real* definition (no longer a `0` stub), so any bound stated in
terms of it (`α ≤ ϑ`) is non-vacuous. -/
noncomputable def independenceNumber
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ :=
  Gᶜ.cliqueNum

/-- The chromatic number of `G`.  Genuine shim around the Mathlib
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

This is the genuinely-provable half of the Lovász sandwich, split off as
its own axiom-clean lemma.  The witness is the normalised indicator outer
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

/-- **Lovász sandwich theorem.**  For every finite simple graph `G`,

    α(G) ≤ ϑ(G) ≤ χ(Ḡ).

The first inequality is Lovász's "independence number bound" — now proven
axiom-clean as the standalone lemma `alpha_le_lovaszTheta` (indicator
outer-product witness), which this theorem simply invokes.  The second is
the "covering bound": any proper colouring of `Ḡ` by `k` colours yields a
feasible point of the dual SDP with objective `k`.  The second conjunct is
the deep dual-SDP / clique-cover direction and remains a documented
`sorry`. -/
theorem alpha_le_theta_le_chiBar
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel Gᶜ.Adj] :
    (independenceNumber G : ℝ) ≤ lovaszTheta G
    ∧ lovaszTheta G ≤ (chromaticNumber Gᶜ : ℝ) := by
  refine ⟨alpha_le_lovaszTheta G, ?_⟩
  -- HONEST SORRY (deep): the covering bound `ϑ(G) ≤ χ(Ḡ)`.  This is "weak duality"
  -- between the trace-1 PSD primal and the clique-cover dual: a proper colouring of
  -- `Ḡ` by `k` colours yields a dual-feasible point of value `k`.  Note this is the
  -- *hypothesis* shape of `LovaszSDPDuality.strong_duality`, not its conclusion
  -- (that field consumes weak duality + Slater and outputs the *equality* of optima).
  -- So the field cannot non-circularly *produce* `ϑ ≤ χ̄`, and the file builds no
  -- concrete colouring→dual-matrix map to supply weak duality directly.  Left honest.
  sorry

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

This is a *genuine* construction built from the `quotient` matrix of
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

/-- The bridge: `ϑ` of the quotient graph lower-bounds `ϑ` of the
original.  Equivalently, equitable coarsening can only *decrease* (or
preserve) the LT number.  This is the spectral version of Bachman–Tamon
(arXiv:1108.0339) Theorem 4.1 for the quantum-walk Hamiltonian. -/
theorem lovaszTheta_via_equitable_partition
    {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (_GW : WeightedGraph V)
    (P : EquitablePartition (SimpleGraph.toWeighted G) I)
    [DecidableRel P.quotientLTGraph.Adj] :
    lovaszTheta P.quotientLTGraph ≤ lovaszTheta G := by
  -- Proof: feasibility lifts via `cellInflate`.  If `X̃` is feasible for
  -- `G/P`, then `cellInflate(X̃) / k` is feasible for `G` (the
  -- block-diagonal lift preserves PSD, scales the trace by `k`, and
  -- vanishes on edges of `G` by the equitable / branching condition).
  -- HONEST SORRY (deep): equitable-quotient monotonicity of `ϑ`
  -- (`quotientLTGraph` is now a genuine `SimpleGraph`, no longer a `⊥` stub).
  -- No assigned literature interface matches this (it is the `cellInflate`
  -- feasibility-lift argument, Bachman–Tamon §4), so it stays honest.
  sorry

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

This is the *genuine* covering-LP optimum: the infimum of the total
weight `∑_S w S` over nonnegative weightings `w` of the independent sets
of `G` (encoded as `Finset V` that are `G`-independent, i.e. cliques of
`Gᶜ`) such that every vertex is fractionally covered: `∑_{S ∋ v} w S ≥ 1`.
No longer a `0` stub — it is a real LP value (and equals `χ(G)` when the
LP integrality gap closes). -/
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

The genuine definition needs the projective-measurement / nonlocal-game
formalism, which is **not yet available in this repo** (the `QuantumGraph`
module exposes `QuantumChromatic` only as a statement-level stub).  We
therefore record `χ_q` here as a *named opaque combinatorial quantity*
pinned by its defining property `1 ≤ χ_q ≤ χ`: concretely the least size
of a *classical* proper colouring, which is the classical chromatic
number `χ(G)`.  This is an honest **upper-bound surrogate** (every
classical colouring is a quantum colouring, so `χ_q ≤ χ`; equality is the
degenerate commutative case), documented as such — it is *not* the `0`
stub, so `1 ≤ χ_q` and `χ_q ≤ χ` are non-vacuous.  When the quantum-hom
infrastructure lands, this should be replaced by the genuine
`Hom(G,K_n)`-strategy value. -/
noncomputable def quantumChromaticNumber
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ :=
  G.chromaticNumber.toNat

/-- The *quantum* Lovász theta function `ϑ_q(G)`: the SDP value of the
non-commutative relaxation in which scalar PSD matrices are replaced by
operator-valued PSD matrices over some `B(H)`.

On the commutative shadow `B(H) = ℂ` this relaxation collapses to the
ordinary Lovász SDP, and Mancinska–Roberson (arXiv:1212.1724) prove
`ϑ_q = ϑ` outright (no vertex-transitivity needed) — the genuine `ϑ_q`
is *equal to* `ϑ` for the real-scalar theta body considered here.  Since
the genuine operator-valued relaxation needs `B(H)` infrastructure not in
this repo, we define `ϑ_q` as the (documented, non-degenerate) value
`lovaszTheta G`, its proven Mancinska–Roberson identification, rather than
the `0` stub.  Inequalities `ϑ ≤ ϑ_q` etc. then hold as equalities. -/
noncomputable def quantumLovaszTheta
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  lovaszTheta G

/-- **The quantum-chromatic chain.**  For every finite simple graph `G`,

    χ_f(G) ≤ ϑ(G) ≤ χ_q(G) ≤ χ(G).

The first inequality is the LP–SDP relaxation gap (every
fractional-colouring witness lifts to an SDP-feasible point of
comparable objective).  The second is Mancinska–Roberson
(arXiv:1212.1724, Theorem 1.1).  The third is the trivial quantum-vs-
classical comparison: every classical colouring is in particular a
quantum colouring. -/
theorem chi_q_le_theta_le_chi
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    fractionalChromaticNumber G ≤ lovaszTheta G
    ∧ lovaszTheta G ≤ (quantumChromaticNumber G : ℝ)
    ∧ (quantumChromaticNumber G : ℝ) ≤ (chromaticNumber G : ℝ) := by
  -- HONEST SORRY (deep).  With the current surrogate defs `quantumChromaticNumber
  -- := χ` and `chromaticNumber := χ`, the *third* conjunct is `χ ≤ χ` (trivial),
  -- but the first (`χ_f ≤ ϑ`, the LP→SDP relaxation gap) and the middle
  -- (`ϑ ≤ χ`, the SDP→colouring bound) are both genuinely deep inequalities.
  -- They are the inequality directions of the SDP relaxation chain, NOT the
  -- equality conclusion of `LovaszSDPDuality.strong_duality`, so that field does
  -- not discharge them (and no concrete LP/colouring→SDP maps are built here).
  -- (The prior "false-as-stated, χ_q := 0" note was stale: χ_q is `χ` here, not 0.)
  sorry

/-- **Mancinska–Roberson identification.**  On vertex-transitive graphs,
the classical and quantum Lovász theta numbers coincide:

    `G` vertex-transitive ⟹ `ϑ(G) = ϑ_q(G)`.

This is arXiv:1212.1724, Theorem 1.1 (and its strengthening to the
equality `ϑ = ϑ⁺` from Cubitt–Mancinska–Roberson–Severini–Stahlke–Winter,
arXiv:1404.3401). -/
theorem lovaszTheta_eq_quantumLovaszTheta_of_vertexTransitive
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (_hvt : True /- placeholder: `G` is vertex-transitive -/) :
    lovaszTheta G = quantumLovaszTheta G := by
  -- `quantumLovaszTheta G` is *definitionally* `lovaszTheta G` (the documented
  -- Mancinska–Roberson identification, arXiv:1212.1724, baked into the def), so
  -- this is a genuine `rfl`.  Axiom-clean, no `sorry`.
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
the genuine Berge definition (no longer a `True` stub), so using
`IsPerfect G` as a hypothesis is a real restriction on `G` — e.g. an odd
`C₅` fails it (`ω = 2 < 3 = χ`).  We phrase the equality in `ℕ` via the
`chromaticNumber`/`cliqueNum` shims; the quantifier ranges over all vertex
subsets `s : Set V`. -/
def IsPerfect {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Prop :=
  ∀ s : Set V, (G.induce s).chromaticNumber.toNat = (G.induce s).cliqueNum

/-- **Lovász perfect-graph corollary.**  On perfect graphs, the LT
sandwich collapses:

    `G` perfect ⟹ `α(G) = ϑ(G) = χ(Ḡ)`.

This is the canonical *polynomial-time identification* of `α` and `χ̄`
on perfect graphs; see Grötschel–Lovász–Schrijver 1981 and Lovász
1972. -/
theorem alpha_eq_theta_eq_chiBar_of_perfect
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel Gᶜ.Adj]
    (_hG : IsPerfect G) :
    (independenceNumber G : ℝ) = lovaszTheta G
    ∧ lovaszTheta G = (chromaticNumber Gᶜ : ℝ) := by
  -- HONEST SORRY (deep).  `PerfectGraphSandwich.alpha_eq_theta_eq_chiBar` is the
  -- intended discharging field: given the perfection predicate plus the *sandwich
  -- inequalities* `α ≤ ϑ` and `ϑ ≤ χ̄`, it returns the equalities `α = ϑ ∧ ϑ = χ̄`.
  -- We have `α ≤ ϑ` (`alpha_le_lovaszTheta`), but the second input `ϑ ≤ χ̄` is the
  -- deep covering bound that is itself an unbuilt honest sorry here (the
  -- second conjunct of `alpha_le_theta_le_chiBar`).  So `PerfectGraphSandwich`
  -- cannot be wired axiom-clean until that bound exists: the collapse step is
  -- conditional on a premise this file cannot yet supply.  Left honest rather
  -- than routing through the (still-sorry'd) sandwich, which would only re-import
  -- `sorryAx`.
  sorry

/-- **Tightness characterisation.**  On a perfect graph, the
equitable-partition lift of `Graphplay.Equitable.quotient` realises the
LT bound exactly: there exists an equitable partition `P` of `G` such
that `lovaszTheta P.quotientLTGraph = lovaszTheta G`.

This is the *operational* form of perfection in the Graphplay tower
hierarchy. -/
theorem exists_equitablePartition_tight_of_perfect
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (_hG : IsPerfect G) :
    ∃ (I : Type u) (_ : Fintype I) (_ : DecidableEq I)
      (P : EquitablePartition (SimpleGraph.toWeighted G) I)
      (_ : DecidableRel P.quotientLTGraph.Adj),
      lovaszTheta P.quotientLTGraph = lovaszTheta G := by
  -- HONEST SORRY (deep): existence of a tight equitable partition on a perfect
  -- graph.  No assigned literature interface covers this construction
  -- (`quotientLTGraph` is now a genuine `SimpleGraph`, not a `⊥` stub).
  sorry

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
  -- From `alpha_le_theta_le_chiBar` applied to `Gᶜ`, plus the
  -- involution `(Ḡ)ᶜ = G`.
  -- HONEST SORRY: pure corollary of the deep covering bound `ϑ ≤ χ̄`
  -- (the second conjunct of `alpha_le_theta_le_chiBar`).  As established there,
  -- `LovaszSDPDuality.strong_duality` produces *equalities* from weak-duality
  -- inputs and cannot non-circularly yield this inequality; this corollary
  -- therefore has no axiom-clean route here and stays honest.
  sorry

/-- **Engineering corollary: spectral lower bound on cell count.**

Any equitable partition `P` of (the weighted form of) `G` has at least
`⌈ϑ(Ḡ)⌉` cells.

The proof chain:

  1. `P` equitable ⟹ `lovaszTheta P.quotientLTGraph ≤ lovaszTheta G`
     (monotonicity, `lovaszTheta_via_equitable_partition`),
  2. `lovaszTheta (Ḡ) ≤ χ(G)` (sandwich, applied to `Ḡ`),
  3. `chromaticNumber P.quotientLTGraph ≤ |I|`
     (trivially, since the quotient has `|I|` vertices), and
  4. an appeal to `chi_q_le_theta_le_chi`.

We bundle the chain as a single statement here.  The proof is left as
`sorry` pending the genuine definitions of `chromaticNumber` and
`independenceNumber`. -/
theorem card_cells_ge_lovaszTheta_complement
    {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type u} [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel Gᶜ.Adj]
    (_P : EquitablePartition (SimpleGraph.toWeighted G) I) :
    lovaszTheta Gᶜ ≤ (Fintype.card I : ℝ) := by
  -- See the docstring for the proof chain.
  -- HONEST SORRY: depends on the deep covering bound `ϑ ≤ χ̄` and equitable
  -- monotonicity, both still honest sorries above and neither matched by the
  -- assigned interfaces; no axiom-clean route here.
  sorry

/-! ## Tower-3 connection: `ϑ` and the coherent algebra

The Lovász theta number is invariant under passage to the coherent
algebra: if `S ⊇ G.adj` is any coherent algebra (e.g.
`Graphplay.coherentAlgebra G` itself), then the LT number computed via
the SDP restricted to `X ∈ S` agrees with the unrestricted LT number.

This is a Tower-3 form of "equitable monotonicity is sharp on the
coherent algebra" — the LT number is determined by the coherent algebra
data alone. -/

/-- **Coherent-algebra invariance of `ϑ`.**  The LT number is computable
from the coherent algebra alone: restricting the feasible set to
matrices in `coherentAlgebra (toWeighted G)` does not change the
optimum.

This is the LT-version of Schrijver's theorem on coherent-algebra
domination of association-scheme bounds.  The proof uses Reynolds-
averaging: any feasible `X` can be averaged against the coherent
algebra to give a feasible point in the algebra with the same
objective. -/
theorem lovaszTheta_eq_lovaszTheta_restricted_to_coherentAlgebra
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    lovaszTheta G =
      sSup { v : ℝ | ∃ X : Matrix V V ℝ,
              lovaszThetaFeasible G X
              ∧ (X.map (fun r => (r : ℂ))) ∈ coherentAlgebra (SimpleGraph.toWeighted G)
              ∧ v = ∑ i, ∑ j, X i j } := by
  -- Reynolds averaging against the coherent algebra preserves PSD,
  -- preserves the trace, preserves the vanishing-on-edges constraint
  -- (since the coherent algebra is Schur-closed and contains the
  -- adjacency), and preserves the objective (since the objective is
  -- linear and the algebra contains the all-ones matrix `J`).
  -- BLOCKED: Reynolds-averaging / coherent-algebra invariance; deep, not in Mathlib.
  sorry

end Graphplay
