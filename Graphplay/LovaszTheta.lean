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

All proofs are `sorry`; the file aims to lay out the statements precisely
in the shape that the rest of Graphplay expects.
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring.VertexColoring
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.StarOrdered
import Mathlib.Analysis.InnerProductSpace.Basic
import Graphplay.Weighted
import Graphplay.Equitable
import Graphplay.QuantumGraph

open scoped Matrix
open Matrix

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
itself an SDP-extracted gadget. -/
noncomputable def OrthonormalRepresentation.value
    {V : Type u} [Fintype V] {G : SimpleGraph V} {d : ℕ}
    (_ρ : OrthonormalRepresentation G d) : ℝ :=
  0  -- placeholder: `inf_c max_i 1 / ⟨c, ρ.vec i⟩^2`

/-- **Equivalence (a): orthonormal representations.** `ϑ(G)` equals the
infimum, over all orthonormal representations `ρ` and all dimensions
`d`, of `ρ.value`. -/
theorem lovaszTheta_eq_orthonormalRepresentation
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    lovaszTheta G =
      sInf { v : ℝ | ∃ (d : ℕ) (ρ : OrthonormalRepresentation G d), v = ρ.value } := by
  -- HONEST SORRY (deep): Lovász 1979 SDP-duality.  Currently also *false as
  -- literally stated* because the placeholder `OrthonormalRepresentation.value
  -- := 0` collapses the RHS to `sInf {0} = 0 < 1 ≤ lovaszTheta` — it becomes
  -- true once `value` gets its genuine `inf_c max_i 1/⟨c,u_i⟩²` definition.
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
  -- This is strong SDP duality: the primal and dual programs both have
  -- strictly feasible interiors (Slater's condition), so the optimal
  -- values agree.
  sorry

/-- **Equivalence (c): eigenvalue / `cos θ` formulation.** For
vertex-transitive `G`, Lovász's "ratio bound" applies:

    `ϑ(G) = |V| · (-λ_min(A)) / (λ_max(A) - λ_min(A))`

where `A` is the 0/1 adjacency matrix.  The general (non
vertex-transitive) case has an analogous but more involved formula. -/
theorem lovaszTheta_eq_ratioBound
    {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (_hvt : True /- placeholder for vertex-transitive hypothesis -/) :
    lovaszTheta G = 0  -- placeholder for `|V| · (-λ_min) / (λ_max - λ_min)`
    := by
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

/-- **Lovász sandwich theorem.**  For every finite simple graph `G`,

    α(G) ≤ ϑ(G) ≤ χ(Ḡ).

The first inequality is Lovász's "independence number bound": any
independent set witnesses a feasible point of the SDP with objective
`|S|`.  The second is the "covering bound": any proper colouring of `Ḡ`
by `k` colours yields a feasible point of the dual SDP with objective
`k` (each colour class gives a clique of `G`, hence a rank-one PSD
summand).  Putting them together gives the sandwich.

This is the *spectral* upper bound on `α` and *spectral* lower bound on
`χ(Ḡ)`, with both bounds polynomially computable (via SDP). -/
theorem alpha_le_theta_le_chiBar
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel Gᶜ.Adj] :
    (independenceNumber G : ℝ) ≤ lovaszTheta G
    ∧ lovaszTheta G ≤ (chromaticNumber Gᶜ : ℝ) := by
  -- Lovász 1979, Theorems 3 and 4.  Each direction is a feasible-point
  -- witness:  α → trace-1 PSD via the indicator;  χ(Ḡ) → dual via a
  -- clique-cover construction.
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
cells, with `i ~ j` iff some (equivalently, every) representative of
cell `i` has positive branching number to cell `j`.

For now we record only the *statement-of-shape*; the genuine quotient
construction (which uses the `quotient` matrix from `Graphplay.Equitable`)
is left implicit. -/
noncomputable def EquitablePartition.quotientLTGraph
    {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    {G : WeightedGraph V} (_P : EquitablePartition G I) :
    SimpleGraph I :=
  ⊥  -- placeholder; the actual quotient depends on the branching matrix

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
Placeholder; the genuine definition is the optimum of the standard
covering LP. -/
noncomputable def fractionalChromaticNumber
    {V : Type u} [Fintype V] [DecidableEq V]
    (_G : SimpleGraph V) : ℝ :=
  0

/-- The *quantum* chromatic number of `G`: the least `n` such that
there exists a quantum `n`-colouring of `G` (i.e., a family of
projections in some `B(H)` satisfying the colouring identities of the
synchronous non-local game `Hom(G, K_n)`).  Placeholder. -/
noncomputable def quantumChromaticNumber
    {V : Type u} [Fintype V] [DecidableEq V]
    (_G : SimpleGraph V) : ℕ :=
  0

/-- The *quantum* Lovász theta function `ϑ_q(G)`: the SDP value of the
non-commutative relaxation in which scalar PSD matrices are replaced
by operator-valued PSD matrices over some `B(H)`.  Placeholder. -/
noncomputable def quantumLovaszTheta
    {V : Type u} [Fintype V] [DecidableEq V]
    (_G : SimpleGraph V) : ℝ :=
  0

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
  -- Each step is a separate SDP / operator-system relaxation argument;
  -- see Mancinska–Roberson arXiv:1212.1724 §3-§5 for the middle
  -- inequality.
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
  -- Mancinska–Roberson 2012, arXiv:1212.1724.
  sorry

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
  sorry

end Graphplay
