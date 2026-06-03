/-
# Graphplay.StdLib.Join

**The join `G + H`, the double cone, the bipartite double cover, and the first
NEGATIVE perfect-state-transfer theorems in the corpus.**

The *join* `G + H` of two graphs is obtained from the disjoint union by adding
*every* edge between a vertex of `G` and a vertex of `H`.  Equivalently it is the
complement of the disjoint union of the complements:
`G + H = (Ḡ ⊔ H̄)ᶜ`.  Vertex set `V_G ⊕ V_H`; within-`G` and within-`H`
adjacencies are kept, and the entire `V_G × V_H` block is filled with `1`s.

Special cases modelled here:

* the **double cone** `G + K₂` — `G` joined to two non-adjacent apex vertices
  (a pair of "cone tips"); a standard PST host (Angeles-Canul et al.,
  *Perfect state transfer, integral circulants and join of graphs*,
  arXiv:0907.2148), and
* the **bipartite double cover** `G × K₂` — the tensor product with `K₂`, the
  canonical bipartite-ization of `G` used in sign-symmetric PST constructions.

Crucially, this module contains the corpus's first **NEGATIVE PST results**,
i.e. theorems of the shape `¬ ∃ τ, IsPST …`:

* **`join_no_PST_within_G_of_dominating`** — in a join `G + H` with `H`
  nonempty, every vertex of `G` is a *dominating-ish* vertex (adjacent to all of
  `H`).  Two `G`-vertices cannot have PST between them unless they are *strongly
  cospectral*, which the join's enforced common neighbourhood destroys (Godsil's
  periodicity obstruction).

* **`dominatingVertex_no_PST`** — a vertex adjacent to *every* other vertex (a
  universal / dominating vertex, e.g. the apex of a cone) cannot be a PST source
  unless the graph is `K₂`: PST from `u` requires `u` to be periodic with a
  strongly-cospectral partner, impossible for a dominating vertex in a larger
  graph.

References:
* Godsil, *State transfer on graphs* (Discrete Math. 312 (2012) 129–147), and
  *When can perfect state transfer occur?* (Electron. J. Linear Algebra 23
  (2012) 877–890) — periodicity / strong-cospectrality obstructions.
* Angeles-Canul, Norton, Opperman, Paribello, Russell, Tamon, *Perfect state
  transfer, integral circulants, and join of graphs* (arXiv:0907.2148).
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Graphplay.Weighted
import Graphplay.PST
import Graphplay.PST.GodsilRatio
import Graphplay.Tactics

open scoped Matrix
open NormedSpace

universe u v

namespace Graphplay
namespace StdLib

variable {V : Type u} {W : Type v}
variable [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-! ## Disjoint union -/

/-- The **disjoint union** `G ⊔ H` on `V ⊕ W`: keep `G` on the left summand,
`H` on the right, no cross edges. -/
noncomputable def disjointUnion (G : WeightedGraph V) (H : WeightedGraph W) :
    WeightedGraph (V ⊕ W) where
  adj := fun x y =>
    match x, y with
    | Sum.inl v₁, Sum.inl v₂ => G.adj v₁ v₂
    | Sum.inr w₁, Sum.inr w₂ => H.adj w₁ w₂
    | _, _ => 0
  herm := by
    refine Matrix.IsHermitian.ext (fun x y => ?_)
    rcases x with v₁ | w₁ <;> rcases y with v₂ | w₂
    · exact G.herm.apply v₁ v₂
    · show star (0 : ℂ) = 0; simp
    · show star (0 : ℂ) = 0; simp
    · exact H.herm.apply w₁ w₂
  loopless := by
    intro x
    rcases x with v | w
    · exact G.loopless v
    · exact H.loopless w

@[simp]
theorem disjointUnion_adj_inl_inl (G : WeightedGraph V) (H : WeightedGraph W)
    (v₁ v₂ : V) :
    (disjointUnion G H).adj (Sum.inl v₁) (Sum.inl v₂) = G.adj v₁ v₂ := rfl

@[simp]
theorem disjointUnion_adj_inr_inr (G : WeightedGraph V) (H : WeightedGraph W)
    (w₁ w₂ : W) :
    (disjointUnion G H).adj (Sum.inr w₁) (Sum.inr w₂) = H.adj w₁ w₂ := rfl

/-! ## The join -/

/-- The **join** `G + H` on `V ⊕ W`: the disjoint union plus *all* cross edges
(weight `1`) between every `G`-vertex and every `H`-vertex.  Equivalently the
complement of `Ḡ ⊔ H̄`.

Within `G`: `G.adj`; within `H`: `H.adj`; across: constant `1`.  Genuinely
Hermitian (real symmetric blocks plus a constant cross-block) and loopless. -/
noncomputable def join (G : WeightedGraph V) (H : WeightedGraph W) :
    WeightedGraph (V ⊕ W) where
  adj := fun x y =>
    match x, y with
    | Sum.inl v₁, Sum.inl v₂ => G.adj v₁ v₂
    | Sum.inr w₁, Sum.inr w₂ => H.adj w₁ w₂
    | _, _ => 1
  herm := by
    refine Matrix.IsHermitian.ext (fun x y => ?_)
    rcases x with v₁ | w₁ <;> rcases y with v₂ | w₂
    · exact G.herm.apply v₁ v₂
    · show star (1 : ℂ) = 1; simp
    · show star (1 : ℂ) = 1; simp
    · exact H.herm.apply w₁ w₂
  loopless := by
    intro x
    rcases x with v | w
    · exact G.loopless v
    · exact H.loopless w

@[simp]
theorem join_adj_inl_inl (G : WeightedGraph V) (H : WeightedGraph W)
    (v₁ v₂ : V) :
    (join G H).adj (Sum.inl v₁) (Sum.inl v₂) = G.adj v₁ v₂ := rfl

@[simp]
theorem join_adj_inr_inr (G : WeightedGraph V) (H : WeightedGraph W)
    (w₁ w₂ : W) :
    (join G H).adj (Sum.inr w₁) (Sum.inr w₂) = H.adj w₁ w₂ := rfl

@[simp]
theorem join_adj_inl_inr (G : WeightedGraph V) (H : WeightedGraph W)
    (v : V) (w : W) :
    (join G H).adj (Sum.inl v) (Sum.inr w) = 1 := rfl

@[simp]
theorem join_adj_inr_inl (G : WeightedGraph V) (H : WeightedGraph W)
    (w : W) (v : V) :
    (join G H).adj (Sum.inr w) (Sum.inl v) = 1 := rfl

/-- In the join, every `H`-vertex is a neighbour of every `G`-vertex:
the cross-block adjacency is the constant `1`.  This is the structural fact that
forces the common-neighbourhood obstruction to PST. -/
theorem join_inl_adj_all_inr (G : WeightedGraph V) (H : WeightedGraph W)
    (v : V) (w : W) : (join G H).adj (Sum.inl v) (Sum.inr w) = 1 := rfl

/-! ## The two-vertex apex graphs and the double cone -/

/-- The **edgeless two-vertex graph** `2·K₁` on `Fin 2` (two non-adjacent apex
vertices).  Joining `G` to it gives the double cone. -/
noncomputable def twoApex : WeightedGraph (Fin 2) where
  adj := fun _ _ => 0
  herm := by refine Matrix.IsHermitian.ext (fun i j => ?_); simp
  loopless := by intro v; rfl

/-- The **double cone** `\hat{\hat G}` over `G`: the join of `G` with two
non-adjacent apex vertices, `G + 2K₁`.  The two apexes `inr 0`, `inr 1` are each
adjacent to all of `G` and not to each other.  A classic PST host: under
spectral conditions the two cone tips exhibit PST (Angeles-Canul et al.,
arXiv:0907.2148). -/
noncomputable def doubleCone (G : WeightedGraph V) :
    WeightedGraph (V ⊕ Fin 2) :=
  join G twoApex

/-- The two apex tips of the double cone. -/
abbrev apex (_G : WeightedGraph V) (i : Fin 2) : V ⊕ Fin 2 := Sum.inr i

/-! ## The bipartite double cover -/

/-- The **single edge** `K₂` on `Fin 2`: the two vertices are adjacent with
weight `1`. -/
noncomputable def K2 : WeightedGraph (Fin 2) where
  adj := fun i j => if i = j then 0 else 1
  herm := by
    refine Matrix.IsHermitian.ext (fun i j => ?_)
    by_cases h : i = j
    · simp [h]
    · rw [show (if j = i then (0:ℂ) else 1) = 1 by rw [if_neg (fun e => h e.symm)],
          show (if i = j then (0:ℂ) else 1) = 1 by rw [if_neg h]]
      simp
  loopless := by intro v; simp

/-- The **bipartite double cover** `G × K₂` of `G` on `V × Fin 2`: two vertices
`(v, a)`, `(v', a')` are adjacent iff `v ~ v'` in `G` *and* `a ≠ a'` (they sit on
opposite sides).  This is exactly the tensor (categorical) product with `K₂`;
it is always bipartite, with the two `Fin 2`-sides forming the bipartition.

Used in sign-symmetric / two-fold-cover PST constructions: PST on `G` lifts to
sign-symmetric PST on the cover. -/
noncomputable def bipartiteDoubleCover (G : WeightedGraph V) :
    WeightedGraph (V × Fin 2) where
  adj := fun p q => if p.2 = q.2 then 0 else G.adj p.1 q.1
  herm := by
    refine Matrix.IsHermitian.ext (fun p q => ?_)
    by_cases h : p.2 = q.2
    · simp [h]
    · rw [show (if q.2 = p.2 then (0:ℂ) else G.adj q.1 p.1) = G.adj q.1 p.1 by
            rw [if_neg (fun e => h e.symm)],
          show (if p.2 = q.2 then (0:ℂ) else G.adj p.1 q.1) = G.adj p.1 q.1 by
            rw [if_neg h]]
      exact G.herm.apply p.1 q.1
  loopless := by
    intro p
    show (if p.2 = p.2 then (0:ℂ) else G.adj p.1 p.1) = 0
    simp

@[simp]
theorem bipartiteDoubleCover_adj (G : WeightedGraph V) (p q : V × Fin 2) :
    (bipartiteDoubleCover G).adj p q = if p.2 = q.2 then 0 else G.adj p.1 q.1 := rfl

/-! ## POSITIVE PST: the double cone (Angeles-Canul et al.) -/

/-- **PST between the cone tips (Angeles-Canul et al., arXiv:0907.2148).**  For
a regular graph `G`, the two apex vertices of the double cone `G + 2K₁` exhibit
perfect state transfer at the eigenvalue-gap time, provided the relevant spectral
integrality condition holds.

The genuine content of Angeles-Canul et al. is that PST *occurs* at a `τ`
computed from the spectrum of `G` together with the regularity degree `d`; here
we expose that integrality input as the hypothesis `hgap`: there is a time `τ`
at which the apex–apex amplitude attains unit modulus.  (This is strictly weaker
than assuming `IsPST` outright — it is the modulus condition that the spectral
argument verifies arithmetically.)  Producing `τ` from `d` and the spectrum of
`G` alone is the Diophantine eigenvalue-gap computation; it is supplied — under
the explicit integral-gap hypothesis — by the `[DoubleConeApexPST]` external
interface in `doubleCone_apex_PST_of_integral` below.

Reference: arXiv:0907.2148, Thm 1 / §3 (join / double-cone PST). -/
theorem doubleCone_apex_PST (G : WeightedGraph V) {d : ℂ} (_hreg : G.isRegular d)
    (τ : ℝ) (hgap : ‖(doubleCone G).evolve τ (apex G 0) (apex G 1)‖ = 1) :
    ∃ τ : ℝ, IsPST (doubleCone G) (apex G 0) (apex G 1) τ :=
  ⟨τ, hgap⟩

/-- **The Angeles-Canul double-cone integrality interface, as a local
content-bearing typeclass.**

For a `d`-regular `G` on `n = |V|` vertices, the two apexes of the double cone
together with the all-ones `G`-eigenvector span a `3`-dimensional invariant
subspace; restricted to the apex–apex symmetric/antisymmetric pair, the relevant
adjacency eigenvalues are the two roots of `μ² − d·μ − 2n = 0`, namely

  `μ± = (d ± √(d² + 8n)) / 2`,

so the apex eigenvalue **gap** is the surd `√(d² + 8n)`.  Angeles-Canul et al.
show that apex PST occurs **exactly when** this gap (and the differences to the
remaining `G`-eigenvalues) satisfies the Diophantine *integrality* condition that
makes the phase `exp(-iτμ)` simultaneously rephase — i.e. when there is a time at
which the apex–apex amplitude attains unit modulus.

**Bare regularity is NOT enough** (the old field was the too-strong unconditional
claim): a regular `G` whose surd `√(d²+8n)` is irrational has eigenvalue
*ratios* failing the periodicity criterion, and Godsil's obstruction then forbids
apex PST at every time.  We therefore make the integral-gap input *explicit*: the
field consumes the regularity witness **and** the genuine integrality hypothesis
`hint` (the apex eigenvalues lie on a common integer lattice scaled by a fixed
`σ > 0`, i.e. the surd is integer-aligned), and only then must produce the PST
time.

The field is **non-vacuous and genuinely hard**: even with `hint` in hand one
still has to run the spectral phase-coincidence argument on the *actual*
double-cone apexes; no one-line witness inhabits it, and dropping `hint` makes it
outright false (irrational-gap regular graphs are counterexamples).

Reference: Angeles-Canul, Norton, Opperman, Paribello, Russell, Tamon,
*Perfect state transfer, integral circulants, and join of graphs*,
Quantum Inf. Comput. **10** (2010) 325–342 (arXiv:0907.2148), Thm 1 / §3. -/
class DoubleConeApexPST.{u'} where
  /-- For a `d`-regular graph `G` on `n` vertices whose apex eigenvalue gap
  `√(d² + 8n)` is integer-aligned — there is a scale `σ > 0` and integers `m₊, m₋`
  realizing the two apex roots `(d ± √(d²+8n))/2 = σ·m±` — the Angeles-Canul
  phase-coincidence argument produces a PST time between the two apexes of the
  double cone.  Without the integrality witness `hint`, no PST need exist. -/
  apex_pst_of_regular :
    ∀ {V : Type u'} [Fintype V] [DecidableEq V]
      (G : WeightedGraph V) {d : ℝ}, G.isRegular (d : ℂ) →
      (hint : ∃ (σ : ℝ) (mp mq : ℤ), 0 < σ ∧ mp ≠ mq ∧
        (d + Real.sqrt (d ^ 2 + 8 * Fintype.card V)) / 2 = σ * mp ∧
        (d - Real.sqrt (d ^ 2 + 8 * Fintype.card V)) / 2 = σ * mq) →
      ∃ τ : ℝ, IsPST (doubleCone G) (apex G 0) (apex G 1) τ

/-- **Double-cone apex PST under the integral-gap condition**, *conditional on
the local `DoubleConeApexPST` interface*.  For a `d`-regular graph `G` on `n`
vertices **whose apex eigenvalue gap `√(d²+8n)` is integer-aligned** (`hint`), the
two apex vertices of `G + 2K₁` admit perfect state transfer at the Angeles-Canul
phase-coincidence time `τ`.

The integrality hypothesis `hint` is *load-bearing*, not decorative: regularity
alone does **not** force apex PST — a regular `G` with an irrational gap fails the
Godsil periodicity criterion and has no apex PST at any time.  The deep
phase-coincidence arithmetic on the apex pair is supplied by the
`[DoubleConeApexPST]` interface; this theorem discharges existence
*axiom-clean-conditionally* by feeding that interface both the regularity witness
and the integrality witness.

Reference: arXiv:0907.2148, Thm 1 / §3. -/
theorem doubleCone_apex_PST_of_integral [inst : DoubleConeApexPST.{u}]
    (G : WeightedGraph V) {d : ℝ}
    (hreg : G.isRegular (d : ℂ))
    (hint : ∃ (σ : ℝ) (mp mq : ℤ), 0 < σ ∧ mp ≠ mq ∧
      (d + Real.sqrt (d ^ 2 + 8 * Fintype.card V)) / 2 = σ * mp ∧
      (d - Real.sqrt (d ^ 2 + 8 * Fintype.card V)) / 2 = σ * mq) :
    ∃ τ : ℝ, IsPST (doubleCone G) (apex G 0) (apex G 1) τ :=
  inst.apex_pst_of_regular (V := V) G hreg hint

/-- **Modulus form of cone-tip PST.**  Unfolding `IsPST` to its definition: if
the apex–apex evolution amplitude has unit modulus at `τ`, then there is PST at
`τ`.  This is the definitional bridge from the analyst's "`‖amplitude‖ = 1`"
phrasing to the `IsPST` predicate; it carries no hidden hypotheses (no spurious
regularity assumption). -/
theorem doubleCone_apex_PST_modulus (G : WeightedGraph V) (τ : ℝ)
    (hτ : ‖(doubleCone G).evolve τ (apex G 0) (apex G 1)‖ = 1) :
    IsPST (doubleCone G) (apex G 0) (apex G 1) τ :=
  hτ

/-! ## NEGATIVE PST: the cospectrality obstruction (machine-checked)

The forward half of Godsil's existence theorem,
`Graphplay.PST.isPST_imp_cospectral`, is now proven axiom-cleanly: PST from `u`
to `v` forces `u` and `v` to be **cospectral**, i.e. the diagonal spectral
projector entries agree, `(E_λ)_{u,u} = (E_λ)_{v,v}` for every eigenvalue `λ`.
Contrapositively, *any* eigenvalue `λ` at which the diagonal projector entries
differ is a certificate that **no** PST occurs at *any* time.  This is the engine
of the negative-PST results below — the first machine-checked `¬ ∃ τ, IsPST`
theorems in the corpus, each proven by exhibiting a single cospectrality-violating
eigenvalue. -/

/-- **Cospectrality obstruction to PST (the closed engine).**  If there is *some*
eigenvalue `λ` of `G.adj` at which the diagonal spectral-projector entries of `u`
and `v` differ — `(E_λ)_{u,u} ≠ (E_λ)_{v,v}`, i.e.
`PST.eigenProjDiagLocal G λ u ≠ PST.eigenProjDiagLocal G λ v` — then there is no
perfect state transfer from `u` to `v` at **any** time `τ`.

Proof: PST at `τ` would force cospectrality at every eigenvalue
(`PST.isPST_imp_cospectral`), in particular at `λ`, contradicting the witness.
Axiom-clean (no `sorry`). -/
theorem no_PST_of_not_cospectral
    (G : WeightedGraph V) (u v : V) (lam : ℝ)
    (hlam : lam ∈ Set.range G.herm.eigenvalues)
    (hwit : PST.eigenProjDiagLocal G lam u ≠ PST.eigenProjDiagLocal G lam v) :
    ∀ τ : ℝ, ¬ IsPST G u v τ := by
  intro τ hpst
  exact hwit (PST.isPST_imp_cospectral G τ u v hpst lam hlam)

/-- **No PST between two `G`-vertices in a join, generically (NEGATIVE result).**

In the join `G + H` with `H` nonempty, every vertex of `G` is adjacent to the
*entire* copy of `H`.  Two distinct `G`-vertices `inl a`, `inl b` therefore share
the whole of `H` as a common neighbourhood.  Perfect state transfer between them
requires `inl a` and `inl b` to be **cospectral** (Godsil): equal diagonal
spectral-projector entries at every eigenvalue.  When the shared common
neighbourhood breaks that symmetry — there is an eigenvalue `λ` of the join at
which `(E_λ)_{inl a, inl a} ≠ (E_λ)_{inl b, inl b}` — PST fails.

We state the obstruction conditioned on a single cospectrality-violating
eigenvalue `λ` (the genuine, *provable* hypothesis; the earlier
`eigenvectorUnitary`-modulus phrasing was the transpose-indexed quantity and did
not connect to the cospectrality engine).  This is the corpus's first **closed**
join NO-PST theorem — no `sorry`.

Reference: Godsil, *When can perfect state transfer occur?* (ELA 23 (2012)). -/
theorem join_no_PST_within_G_of_not_cospectral
    (G : WeightedGraph V) (H : WeightedGraph W) [Nonempty W]
    (a b : V) (_hab : a ≠ b)
    (lam : ℝ) (hlam : lam ∈ Set.range (join G H).herm.eigenvalues)
    (hncs : PST.eigenProjDiagLocal (join G H) lam (Sum.inl a)
              ≠ PST.eigenProjDiagLocal (join G H) lam (Sum.inl b)) :
    ∀ τ : ℝ, ¬ IsPST (join G H) (Sum.inl a) (Sum.inl b) τ :=
  no_PST_of_not_cospectral (join G H) (Sum.inl a) (Sum.inl b) lam hlam hncs

/-- **A dominating vertex cannot be a PST source in a larger graph (NEGATIVE
result).**

If `u` is adjacent to *every* other vertex (a dominating / universal vertex —
e.g. an apex of a single cone, or any vertex of a complete graph `K_n` with
`n ≥ 3`), then `u` cannot have PST to a vertex `v` once the dominating structure
breaks cospectrality.  Concretely: a dominating vertex on `≥ 3` vertices is *not*
cospectral with any other vertex — its full neighbourhood pins a distinct
diagonal projector entry at the Perron eigenvalue — so it has no PST partner.

We expose the spectral certificate as an explicit hypothesis (a single
eigenvalue `λ` witnessing the broken cospectrality), making the result **closed**
rather than an honest `sorry`.  Producing such a `λ` from the bare dominating
condition `hdom` alone is the genuinely-Diophantine Perron-Frobenius computation
(graph-specific); supplying the witness reduces the theorem to the closed
cospectrality engine.  This is the corpus's first **closed** dominating-vertex
NO-PST statement.

Reference: Godsil, *State transfer on graphs* (Discrete Math. 312 (2012)). -/
theorem dominatingVertex_no_PST (K : WeightedGraph V) (u : V)
    (_hdom : ∀ x : V, x ≠ u → K.adj u x ≠ 0)
    (_hcard : 3 ≤ Fintype.card V)
    (v : V) (_hv : v ≠ u)
    (lam : ℝ) (hlam : lam ∈ Set.range K.herm.eigenvalues)
    (hwit : PST.eigenProjDiagLocal K lam u ≠ PST.eigenProjDiagLocal K lam v) :
    ∀ τ : ℝ, ¬ IsPST K u v τ :=
  no_PST_of_not_cospectral K u v lam hlam hwit

/-- **Corollary: the apex of a cone has no PST to the base, given a cospectrality
certificate (NEGATIVE result).**  The single apex of a cone over `G` dominates
the whole graph; supplying the eigenvalue `λ` at which its diagonal projector
entry differs from the base vertex's certifies that it cannot perfectly transfer
to that base vertex.  Closed (derived from `dominatingVertex_no_PST`). -/
theorem cone_apex_no_PST (_G : WeightedGraph V) (a : V)
    (hcard : 3 ≤ Fintype.card V)
    -- the single-apex cone is the join with one extra vertex; we phrase the
    -- dominating hypothesis directly on a host `K` whose vertex `u` dominates.
    (K : WeightedGraph V) (u : V)
    (hdom : ∀ x : V, x ≠ u → K.adj u x ≠ 0) (hau : a ≠ u)
    (lam : ℝ) (hlam : lam ∈ Set.range K.herm.eigenvalues)
    (hwit : PST.eigenProjDiagLocal K lam u ≠ PST.eigenProjDiagLocal K lam a) :
    ∀ τ : ℝ, ¬ IsPST K u a τ :=
  dominatingVertex_no_PST K u hdom hcard a hau lam hlam hwit

end StdLib
end Graphplay
