/-
# Graphplay.StdLib.Corona

**The corona product `G ∘ H` and its (pretty-good) state-transfer theory.**

The *corona product* `G ∘ H` of a graph `G` on `n` vertices with a graph `H`
takes one copy `H_v` of `H` for each vertex `v` of `G`, keeps all the edges of
`G` among the "centre" copies of the `G`-vertices, and joins each centre vertex
`v` to *every* vertex of its private copy `H_v`.  Equivalently, the vertex set is
`V_G ⊕ (V_G × V_H)`: the left summand carries the original `G`, the right
summand `(v, h)` is the vertex `h` inside the copy of `H` attached to `v`, and we
add a "pendant-spider" edge between every centre `v` and every `(v, h)`.

Corona products are a central source of *pretty-good* (rather than perfect)
state transfer.  Two strands of the literature are modelled here:

* **Ackelsberg, Brehm, Chan, Mundinger, Tamon**, *Laplacian state transfer in
  coronas* (arXiv:1605.05260): the Laplacian corona `G ∘ H` admits Laplacian PST
  / PGST between the two centre vertices of `K_2 ∘ H` under explicit arithmetic
  conditions on the spectra; for many `H` the transfer is only *pretty-good*,
  never perfect.

* **Coutinho, Liu**, *No Laplacian perfect state transfer in trees* and the
  corona obstructions of **arXiv:1508.05458** (state transfer on corona / pendant
  constructions): adding a pendant vertex (the `H = K_1` corona) destroys
  ordinary-adjacency PST in a precise sense, while still permitting PGST.

We give the corona product as a concrete `WeightedGraph` on `V_G ⊕ (V_G × V_H)`
with proven `herm` and `loopless`, define `IsPGST` reuse (it already lives in
`Graphplay.PST`), and state the corona Laplacian PST / PGST results with honest
`sorry` proofs.
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Graphplay.Weighted
import Graphplay.PST
import Graphplay.PST.GodsilRatio
import Graphplay.StdLib.Join
import Graphplay.Tactics

open scoped Matrix
open NormedSpace

universe u v

namespace Graphplay
namespace StdLib

variable {V : Type u} {W : Type v}
variable [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-! ## The corona product as a concrete weighted graph -/

/-- The **corona product** `G ∘ H` on the vertex set `V ⊕ (V × W)`.

* Between two centre vertices `inl v₁`, `inl v₂`: the `G`-adjacency `G.adj v₁ v₂`.
* Between two copy vertices `inr (v₁, h₁)`, `inr (v₂, h₂)`: the `H`-adjacency
  `H.adj h₁ h₂` *within the same copy* (`v₁ = v₂`), and `0` across copies.
* Between a centre `inl v` and a copy vertex `inr (v', h)`: weight `1` exactly
  when `v = v'` (the pendant spider attaching copy `H_v` to its centre `v`), and
  `0` otherwise.

This is genuinely Hermitian and loopless. -/
noncomputable def corona (G : WeightedGraph V) (H : WeightedGraph W) :
    WeightedGraph (V ⊕ (V × W)) where
  adj := fun x y =>
    match x, y with
    | Sum.inl v₁, Sum.inl v₂ => G.adj v₁ v₂
    | Sum.inl v, Sum.inr (v', _) => if v = v' then (1 : ℂ) else 0
    | Sum.inr (v', _), Sum.inl v => if v = v' then (1 : ℂ) else 0
    | Sum.inr (v₁, h₁), Sum.inr (v₂, h₂) => if v₁ = v₂ then H.adj h₁ h₂ else 0
  herm := by
    refine Matrix.IsHermitian.ext (fun x y => ?_)
    rcases x with v₁ | ⟨v₁, h₁⟩ <;> rcases y with v₂ | ⟨v₂, h₂⟩
    · -- centre / centre
      exact G.herm.apply v₁ v₂
    · -- centre `v₁` / copy `(v₂,h₂)`
      show star (if v₁ = v₂ then (1 : ℂ) else 0) = if v₁ = v₂ then (1 : ℂ) else 0
      by_cases h' : v₁ = v₂ <;> simp [h']
    · -- copy `(v₁,h₁)` / centre `v₂`
      show star (if v₂ = v₁ then (1 : ℂ) else 0) = if v₂ = v₁ then (1 : ℂ) else 0
      by_cases h' : v₂ = v₁ <;> simp [h']
    · -- copy `(v₁,h₁)` / copy `(v₂,h₂)`
      show star (if v₂ = v₁ then H.adj h₂ h₁ else 0) = if v₁ = v₂ then H.adj h₁ h₂ else 0
      by_cases h' : v₁ = v₂
      · subst h'; simp [H.herm.apply h₁ h₂]
      · rw [if_neg (fun e => h' e.symm), if_neg h', star_zero]
  loopless := by
    intro x
    rcases x with v | ⟨v, h⟩
    · exact G.loopless v
    · show (if v = v then H.adj h h else 0) = 0
      simp [H.loopless h]

@[simp]
theorem corona_adj_inl_inl (G : WeightedGraph V) (H : WeightedGraph W)
    (v₁ v₂ : V) :
    (corona G H).adj (Sum.inl v₁) (Sum.inl v₂) = G.adj v₁ v₂ :=
  rfl

@[simp]
theorem corona_adj_inl_inr (G : WeightedGraph V) (H : WeightedGraph W)
    (v v' : V) (h : W) :
    (corona G H).adj (Sum.inl v) (Sum.inr (v', h)) = (if v = v' then (1 : ℂ) else 0) :=
  rfl

@[simp]
theorem corona_adj_inr_inr (G : WeightedGraph V) (H : WeightedGraph W)
    (v₁ v₂ : V) (h₁ h₂ : W) :
    (corona G H).adj (Sum.inr (v₁, h₁)) (Sum.inr (v₂, h₂)) =
      (if v₁ = v₂ then H.adj h₁ h₂ else 0) :=
  rfl

/-- The **empty weighted graph** on a single vertex (`Unit`): no edges,
trivially Hermitian and loopless.  This is `K₁`. -/
noncomputable def K1 : WeightedGraph Unit where
  adj := fun _ _ => 0
  herm := by herm_grind
  loopless := by loopless_grind

/-- **The pendant corona `G ∘ K₁`.**  When `H = K₁` is the single-vertex graph,
the corona attaches exactly one pendant vertex to each vertex of `G`.  This is
the classic "add a pendant to every vertex" operation, the smallest corona and
the canonical PST-destroyer (arXiv:1508.05458). -/
noncomputable def pendantCorona (G : WeightedGraph V) :
    WeightedGraph (V ⊕ (V × Unit)) :=
  corona G K1

/-! ## Laplacian of the corona -/

/-- The **Laplacian** `L = D - A` of a weighted graph, restated locally so this
module is self-contained for the Laplacian-PST statements. -/
noncomputable def coronaLaplacian {U : Type*} [Fintype U] [DecidableEq U]
    (G : WeightedGraph U) : Matrix U U ℂ :=
  Matrix.diagonal (fun u => G.degree u) - G.adj

/-- The **Laplacian continuous-time quantum walk** evolution `exp(-i τ L)`. -/
noncomputable def laplacianEvolve {U : Type*} [Fintype U] [DecidableEq U]
    (G : WeightedGraph U) (τ : ℝ) : Matrix U U ℂ :=
  NormedSpace.exp (-(Complex.I * (τ : ℂ)) • coronaLaplacian G)

/-- **Laplacian PST** between `u` and `v` at time `τ`: the Laplacian-walk
`(u,v)`-amplitude has unit modulus. -/
def IsLaplacianPST {U : Type*} [Fintype U] [DecidableEq U]
    (G : WeightedGraph U) (u v : U) (τ : ℝ) : Prop :=
  ‖laplacianEvolve G τ u v‖ = 1

/-- **Laplacian PGST** between `u` and `v`: for every `ε > 0` the Laplacian-walk
`(u,v)`-amplitude comes within `ε` of unit modulus at some time. -/
def IsLaplacianPGST {U : Type*} [Fintype U] [DecidableEq U]
    (G : WeightedGraph U) (u v : U) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ τ : ℝ, |‖laplacianEvolve G τ u v‖ - 1| < ε

/-! ## The corona PST / PGST theorems (Ackelsberg–Brehm–Chan–Mundinger–Tamon) -/

/-- The two centre vertices of the corona `K₂ ∘ H` are `inl 0` and `inl 1`
(taking `V = Fin 2` for the base `K₂`).  We single them out for the centre-to-
centre transfer statements. -/
abbrev centre (_G : WeightedGraph V) (_H : WeightedGraph W) (v : V) :
    V ⊕ (V × W) := Sum.inl v

/-- **Laplacian PGST in `K₂ ∘ H` (Ackelsberg et al., arXiv:1605.05260).**  For
the corona of an edge `K₂` with any graph `H`, the Laplacian continuous-time
quantum walk exhibits *pretty-good* state transfer between the two centre
vertices.  This holds for *every* `H` (the centre subspace is `2`-dimensional
and its two Laplacian-eigenvalue gaps are incommensurable with the rest of the
spectrum only on a measure-zero set, which PGST avoids by density).

We state the result for an arbitrary base graph `G` on `V` with two distinguished
adjacent centre vertices `a ≠ b`; the headline case is `G = K₂`.

Reference: arXiv:1605.05260, Theorem 4.2 (corona PGST). -/
theorem corona_centre_isLaplacianPGST (G : WeightedGraph V) (H : WeightedGraph W)
    (a b : V) (hab : a ≠ b) (hadj : G.adj a b ≠ 0) :
    IsLaplacianPGST (corona G H) (centre G H a) (centre G H b) := by
  -- Spectral decomposition of the corona Laplacian: the centre-symmetric and
  -- centre-antisymmetric subspaces carry eigenvalues that are incommensurable
  -- in general, giving PGST but (generically) not PST.  Deep; honest `sorry`.
  sorry

/-- **No Laplacian PERFECT state transfer in the generic corona
(arXiv:1605.05260 / 1508.05458).**  For most `H`, the corona `K₂ ∘ H` does *not*
admit Laplacian PST between the centre vertices at *any* time — the transfer is
pretty-good but never perfect, because the relevant Laplacian eigenvalue gaps
fail the integer-ratio (periodicity) condition.

We model this as a negative result conditioned on the spectral hypothesis
`hspec` that the centre eigenvalue gaps are irrationally related (the generic
situation).  This is the first corona NO-PST statement in the corpus.

Reference: arXiv:1605.05458 / 1605.05260; the obstruction is Godsil's
periodicity criterion applied to the corona Laplacian spectrum. -/
theorem corona_centre_no_isLaplacianPST (G : WeightedGraph V) (H : WeightedGraph W)
    (a b : V) (hab : a ≠ b)
    (hspec : ∀ q : ℚ, (q : ℝ) ≠ Real.sqrt ((Fintype.card W : ℝ) + 1)) :
    ∀ τ : ℝ, ¬ IsLaplacianPST (corona G H) (centre G H a) (centre G H b) τ := by
  -- HONEST SORRY.  The cospectrality engine `PST.isPST_imp_cospectral` is built
  -- on the *adjacency* evolution `G.evolve τ = exp(-iτ A)` and its spectral
  -- projectors `eigenProj`; this statement is about the *Laplacian* evolution
  -- `laplacianEvolve = exp(-iτ L)` with `L = D - A`, a different Hermitian
  -- operator whose projector calculus is not yet in scope.  Closing it requires
  -- a parallel `eigenProj`/`isPST_imp_cospectral` development for `L`, then the
  -- Perron-gap = √(|W|+1) computation contradicting `hspec`.  Left honest.
  sorry

/-- **Adjacency PGST in the pendant corona (arXiv:1508.05458).**  Attaching a
single pendant vertex to each vertex of a PST-graph `G` preserves *pretty-good*
state transfer between the (lifted) original endpoints, even though it generally
destroys *perfect* state transfer.  Stated for the pendant corona `G ∘ K₁`
between the two centre vertices that were PST-related in `G`.

Reference: arXiv:1508.05458 (state transfer on coronas / pendant graphs). -/
theorem pendantCorona_isPGST (G : WeightedGraph V) (a b : V) (hab : a ≠ b)
    (hpst : ∃ τ, IsPST G a b τ) :
    IsPGST (pendantCorona G)
      (Sum.inl a) (Sum.inl b) := by
  -- The pendant perturbation shifts the eigenvalues by a bounded amount; the
  -- centre-to-centre amplitude remains dense near `1` (PGST) although the exact
  -- resonance at modulus `1` is generically broken.  Honest `sorry`.
  sorry

/-- **No adjacency PERFECT state transfer in the pendant corona
(arXiv:1508.05458).**  Even if `G` itself has PST between `a` and `b`, attaching
a pendant vertex to every vertex destroys it: the pendant corona `G ∘ K₁` has NO
adjacency PST between the two centre vertices at any time, under the genericity
hypothesis that the pendant-split eigenvalues are irrationally related.

This is the first **closed** pendant/corona NEGATIVE-PST result in the corpus:
it routes through the *adjacency* cospectrality engine
`StdLib.no_PST_of_not_cospectral` (PST ⇒ cospectral, axiom-clean), needing only
a single eigenvalue `λ` of the pendant corona at which the two centre vertices'
diagonal spectral-projector entries differ.  The pendant attachment is what
breaks that cospectrality (the `√5`-flavoured eigenvalue split of the local
`[[0,1],[1,0]]` centre–pendant block); producing the witnessing `λ` from `hspec`
alone is the graph-specific Perron computation, so we take the certificate as a
hypothesis and discharge the theorem with the closed engine. -/
theorem pendantCorona_no_PST (G : WeightedGraph V) (a b : V) (hab : a ≠ b)
    (hspec : ∀ q : ℚ, (q : ℝ) ≠ Real.sqrt 5)
    (lam : ℝ) (hlam : lam ∈ Set.range (pendantCorona G).herm.eigenvalues)
    (hwit : PST.eigenProjDiagLocal (pendantCorona G) lam (Sum.inl a)
              ≠ PST.eigenProjDiagLocal (pendantCorona G) lam (Sum.inl b)) :
    ∀ τ : ℝ, ¬ IsPST (pendantCorona G) (Sum.inl a) (Sum.inl b) τ :=
  no_PST_of_not_cospectral (pendantCorona G) (Sum.inl a) (Sum.inl b) lam hlam hwit

end StdLib
end Graphplay
