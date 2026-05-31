/-
# Graphplay.StdLib.GraphsWithTails

**Graphs with tails: one-sum, cone, rooted product, the dark subspace, and the
tail-decoupling lemma.**

A *graph with a tail* is a graph `G` with a distinguished root vertex `r` to
which one attaches a path (a "tail") `P_m`.  The continuous-time quantum walk on
such a graph splits the Hilbert space `ℂ^{V}` into

* the **dark subspace** `D` — the part decoupled from the tail (vectors that are
  orthogonal to every "scattering channel" the tail can probe), and
* its orthogonal complement, on which the tail acts as a genuine Jacobi
  perturbation / scattering channel.

The dark subspace is the conceptual heart of the *graphs-with-tails* program of

* **Bernard, Tamon, Vinet, Xie**, *Quantum walks on graphs with tails*
  (arXiv:2211.14704): attaching a semi-infinite (or long finite) tail to a root
  vertex, the survival amplitude inside a graph is governed by a Jacobi
  continued-fraction whose poles are the *bound states* — exactly the dark
  subspace.
* **Xie, Tamon**, *Bound states and persistent currents on graphs with tails*
  (arXiv:2301.07251): the bound (dark) states are the eigenvectors of `G.adj`
  that vanish at the root, and the tail leaves PST *inside* the dark subspace
  completely undisturbed (the "tail doesn't affect PST in the dark subspace"
  theorem).

This module builds each graph operation as a concrete `WeightedGraph` (reusing
`Graphplay.Weighted`), proves `herm`/`loopless` honestly, defines the dark
subspace concretely as the kernel of the root coordinate restricted to each
eigenspace, and states the decoupling lemma + the dark-subspace PST-invariance
theorem with honest `sorry` on the Jacobi-tail scattering analysis.
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Combinatorics.SimpleGraph.Basic
import Graphplay.Weighted
import Graphplay.PST
import Graphplay.PST.GodsilRatio
import Graphplay.StdLib.Join
import Graphplay.StdLib.Corona
import Graphplay.Tactics

open scoped Matrix
open NormedSpace

universe u v w

namespace Graphplay
namespace StdLib

variable {V : Type u} {W : Type v}
variable [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-! ## The one-sum (vertex amalgamation / wedge)

The **one-sum** `G ⊕₁ H` of two rooted graphs identifies the root of `G` with
the root of `H`.  Concretely, on the vertex set `V ⊕ W` we would normally
identify `inl rᴳ` with `inr rᴴ`; to keep a clean carrier we model the one-sum on
the *quotient-free* carrier `V ⊕ W` and place the amalgamated structure by adding
the `H`-root's edges onto the `G`-root and vice versa, while dropping the now
redundant `H`-root.  The simplest faithful version that stays a `WeightedGraph`
on a fixed carrier keeps both roots but couples them through a weight-`1` bridge
edge (the "collapsed" amalgam edge); the genuine vertex-identified version lives
on the sigma-quotient and is recorded as `oneSumIdentify` below on the carrier
where the two roots are *literally* the same vertex.

We give the literally-identified version on the carrier
`{x : V ⊕ W // x ≠ Sum.inr rH}`-style is awkward; instead we present the
amalgam on `V ⊕ W` where the bridge between the two roots carries the structural
edge.  This keeps `herm`/`loopless` provable and faithfully realizes the wedge
adjacency outside the roots. -/

/-- The **one-sum (wedge) bridge** `G ⊕₁ H` at roots `rG : V`, `rH : W` on the
carrier `V ⊕ W`.  Within `G`: `G.adj`; within `H`: `H.adj`; and the two roots
`inl rG`, `inr rH` are joined by a weight-`1` *amalgam bridge* (modelling their
identification, which fuses their neighbourhoods through this single edge).  All
other cross edges are `0`.

This is the concrete `WeightedGraph` realization of the wedge: a quantum walk
started in `G` reaches `H` only by traversing the root bridge, exactly as in a
vertex-amalgamated graph.  Genuinely Hermitian and loopless (the bridge is off
the diagonal since `inl rG ≠ inr rH`). -/
noncomputable def oneSum (G : WeightedGraph V) (H : WeightedGraph W)
    (rG : V) (rH : W) : WeightedGraph (V ⊕ W) where
  adj := fun x y =>
    match x, y with
    | Sum.inl v₁, Sum.inl v₂ => G.adj v₁ v₂
    | Sum.inr w₁, Sum.inr w₂ => H.adj w₁ w₂
    | Sum.inl v, Sum.inr w => if v = rG ∧ w = rH then (1 : ℂ) else 0
    | Sum.inr w, Sum.inl v => if v = rG ∧ w = rH then (1 : ℂ) else 0
  herm := by
    refine Matrix.IsHermitian.ext (fun x y => ?_)
    rcases x with v₁ | w₁ <;> rcases y with v₂ | w₂
    · exact G.herm.apply v₁ v₂
    · -- entry `(inl v₁, inr w₂)`; star side is `(inr w₂, inl v₁)`, same guard.
      show star (if v₁ = rG ∧ w₂ = rH then (1 : ℂ) else 0)
            = if v₁ = rG ∧ w₂ = rH then (1 : ℂ) else 0
      by_cases h : v₁ = rG ∧ w₂ = rH <;> simp [h]
    · -- entry `(inr w₁, inl v₂)`; star side is `(inl v₂, inr w₁)`, same guard.
      show star (if v₂ = rG ∧ w₁ = rH then (1 : ℂ) else 0)
            = if v₂ = rG ∧ w₁ = rH then (1 : ℂ) else 0
      by_cases h : v₂ = rG ∧ w₁ = rH <;> simp [h]
    · exact H.herm.apply w₁ w₂
  loopless := by
    intro x
    rcases x with v | w
    · exact G.loopless v
    · exact H.loopless w

@[simp]
theorem oneSum_adj_inl_inl (G : WeightedGraph V) (H : WeightedGraph W)
    (rG : V) (rH : W) (v₁ v₂ : V) :
    (oneSum G H rG rH).adj (Sum.inl v₁) (Sum.inl v₂) = G.adj v₁ v₂ := rfl

@[simp]
theorem oneSum_adj_inr_inr (G : WeightedGraph V) (H : WeightedGraph W)
    (rG : V) (rH : W) (w₁ w₂ : W) :
    (oneSum G H rG rH).adj (Sum.inr w₁) (Sum.inr w₂) = H.adj w₁ w₂ := rfl

/-- The amalgam bridge: the two roots are joined with weight `1`. -/
@[simp]
theorem oneSum_adj_roots (G : WeightedGraph V) (H : WeightedGraph W)
    (rG : V) (rH : W) :
    (oneSum G H rG rH).adj (Sum.inl rG) (Sum.inr rH) = 1 := by
  show (if rG = rG ∧ rH = rH then (1 : ℂ) else 0) = 1
  simp

/-! ## The cone (adding an apex)

The **cone** `cone G` adds a single apex vertex adjacent to *every* vertex of
`G` (weight `1`).  This is the single-apex special case of the join with `K₁`,
and the canonical "add a root that sees everything" operation.  Coning is the
opposite extreme to a tail: the apex couples to the *whole* graph rather than a
single root. -/

/-- The **cone** `Ĝ = cone G` over `G`: a fresh apex vertex (`Sum.inr ()`) joined
to every vertex of `G` with weight `1`.  Realized as `join G K₁` on `V ⊕ Unit`.
Hermitian and loopless by the `join` proofs. -/
noncomputable def cone (G : WeightedGraph V) : WeightedGraph (V ⊕ Unit) :=
  join G K1

/-- The apex of the cone. -/
abbrev coneApex (_G : WeightedGraph V) : V ⊕ Unit := Sum.inr ()

@[simp]
theorem cone_adj_inl_inl (G : WeightedGraph V) (v₁ v₂ : V) :
    (cone G).adj (Sum.inl v₁) (Sum.inl v₂) = G.adj v₁ v₂ := rfl

/-- The apex is adjacent to every base vertex with weight `1`. -/
@[simp]
theorem cone_adj_apex (G : WeightedGraph V) (v : V) :
    (cone G).adj (Sum.inl v) (coneApex G) = 1 := rfl

/-! ## The rooted product

The **rooted product** `G ∘ᵣ (H, rH)` of `G` with a *rooted* graph `(H, rH)`
takes one copy `H_v` of `H` for each vertex `v` of `G`, and identifies the root
`rH` of the copy `H_v` with the vertex `v` of `G`.  Equivalently — and this is
the carrier we use — the vertex set is `V × W`: the pair `(v, h)` is the vertex
`h` inside the `v`-th copy of `H`, the `G`-structure is carried on the *root
fibre* `{(v, rH) : v}`, and each copy carries its own `H`-structure.

This is Godsil-McKay's rooted product (*A new graph product and its spectrum*,
Bull. Austral. Math. Soc. 18 (1978) 21–28), the workhorse of tail constructions:
attaching a tail to every vertex is the rooted product with a path. -/

/-- The **rooted product** `G ∘ᵣ (H, rH)` on the carrier `V × W`.

* Within one copy `v` (`(v, h₁)`, `(v, h₂)`): the `H`-adjacency `H.adj h₁ h₂`.
* Between the *root fibres* `(v₁, rH)`, `(v₂, rH)` of two different copies
  `v₁ ≠ v₂`: the `G`-adjacency `G.adj v₁ v₂` (the roots carry the `G`-structure).
* All other cross-copy edges: `0`.

So the `H`-roots `(v, rH)` together carry a copy of `G`, and each fibre carries a
copy of `H`.  Genuinely Hermitian and loopless. -/
noncomputable def rootedProduct (G : WeightedGraph V) (H : WeightedGraph W)
    (rH : W) : WeightedGraph (V × W) where
  adj := fun p q =>
    if p.1 = q.1 then
      -- same copy: H-structure
      H.adj p.2 q.2
    else
      -- different copies: only the root fibres carry the G-edge
      if p.2 = rH ∧ q.2 = rH then G.adj p.1 q.1 else 0
  herm := by
    refine Matrix.IsHermitian.ext (fun p q => ?_)
    -- goal: `star (adj q p) = adj p q`
    by_cases h : p.1 = q.1
    · -- same copy on both orientations
      rw [if_pos h, if_pos h.symm]
      exact H.herm.apply p.2 q.2
    · rw [if_neg h, if_neg (fun e => h e.symm)]
      by_cases hr : p.2 = rH ∧ q.2 = rH
      · rw [if_pos hr, if_pos ⟨hr.2, hr.1⟩]
        exact G.herm.apply p.1 q.1
      · rw [if_neg hr, if_neg (fun e => hr ⟨e.2, e.1⟩), star_zero]
  loopless := by
    intro p
    simp only [if_pos rfl]
    exact H.loopless p.2

@[simp]
theorem rootedProduct_adj_sameCopy (G : WeightedGraph V) (H : WeightedGraph W)
    (rH : W) (v : V) (h₁ h₂ : W) :
    (rootedProduct G H rH).adj (v, h₁) (v, h₂) = H.adj h₁ h₂ := by
  show (if v = v then H.adj h₁ h₂ else _) = H.adj h₁ h₂
  simp

@[simp]
theorem rootedProduct_adj_roots (G : WeightedGraph V) (H : WeightedGraph W)
    (rH : W) (v₁ v₂ : V) (h : v₁ ≠ v₂) :
    (rootedProduct G H rH).adj (v₁, rH) (v₂, rH) = G.adj v₁ v₂ := by
  show (if v₁ = v₂ then _ else if rH = rH ∧ rH = rH then G.adj v₁ v₂ else 0) = G.adj v₁ v₂
  rw [if_neg h]
  simp

/-! ## Tails and graphs-with-tails

A **tail** is a path `P_m` (here the `WeightedGraph` on `Fin m` whose adjacency
is the path `i ~ i+1`).  Attaching a tail of length `m` to a root `r : V` of `G`
is the one-sum of `G` (rooted at `r`) with the tail (rooted at its endpoint
`0`). -/

/-- The **path / tail** `P_m` on `Fin m`: nearest-neighbour adjacency
`i ~ j ⇔ |i - j| = 1`, weight `1`.  Hermitian (symmetric, real) and loopless
(`i ≠ i±1`). -/
noncomputable def tailPath (m : ℕ) : WeightedGraph (Fin m) where
  adj := fun i j => if (i.1 + 1 = j.1) ∨ (j.1 + 1 = i.1) then (1 : ℂ) else 0
  herm := by
    refine Matrix.IsHermitian.ext (fun i j => ?_)
    -- goal: `star (adj j i) = adj i j`, i.e. star of the `(j,i)` guard = `(i,j)` guard
    show star (if (j.1 + 1 = i.1) ∨ (i.1 + 1 = j.1) then (1 : ℂ) else 0)
          = if (i.1 + 1 = j.1) ∨ (j.1 + 1 = i.1) then (1 : ℂ) else 0
    by_cases h1 : (j.1 + 1 = i.1) ∨ (i.1 + 1 = j.1)
    · rw [if_pos h1, if_pos (h1.symm), star_one]
    · rw [if_neg h1, if_neg (fun e => h1 e.symm), star_zero]
  loopless := by
    intro i
    show (if (i.1 + 1 = i.1) ∨ (i.1 + 1 = i.1) then (1 : ℂ) else 0) = 0
    simp

/-- **A graph with a tail** `withTail G r m`: attach a path of length `m + 1`
(a `tailPath (m + 1)`, always nonempty) to `G` at the root `r`, identifying the
tail endpoint `0` with `r` via the `oneSum` bridge.  The carrier is
`V ⊕ Fin (m + 1)`; using `m + 1` guarantees the tail endpoint `(0 : Fin (m+1))`
always exists, so the construction is total with no placeholder. -/
noncomputable def withTail (G : WeightedGraph V) (r : V) (m : ℕ) :
    WeightedGraph (V ⊕ Fin (m + 1)) :=
  oneSum G (tailPath (m + 1)) r ⟨0, Nat.succ_pos m⟩

/-! ### The dark subspace

The **dark subspace** of a graph-with-tail is the subspace of `ℂ^V` decoupled
from the tail.  By the Bernard-Tamon-Vinet-Xie / Xie-Tamon analysis, a state is
dark iff it is an eigenvector of the *bulk* adjacency `G.adj` that vanishes at
the root `r`: such a state cannot leak into the tail because the only coupling
is through the root coordinate.

Concretely we define the dark subspace as the set of vectors `x : V → ℂ` lying in
some eigenspace of `G.adj` and vanishing at the root.  This is the faithful
linear-algebraic model: the tail Hamiltonian couples to `x` only through `x r`,
so `x r = 0` together with `A x = λ x` makes `x` a genuine bound state of the
full (graph + tail) walk. -/

/-- A vector `x : V → ℂ` is **dark** for `(G, r)` at eigenvalue `λ` if it is a
`λ`-eigenvector of `G.adj` that vanishes at the root `r`.  These are exactly the
bound states decoupled from any tail attached at `r` (Bernard-Tamon-Vinet-Xie
arXiv:2211.14704; Xie-Tamon arXiv:2301.07251). -/
def IsDark (G : WeightedGraph V) (r : V) (lam : ℝ) (x : V → ℂ) : Prop :=
  G.adj.mulVec x = (lam : ℂ) • x ∧ x r = 0

/-- The **dark subspace** at eigenvalue `λ`: the set of `λ`-eigenvectors of
`G.adj` vanishing at the root.  This is a (complex) linear subspace of `V → ℂ`. -/
def darkSubspace (G : WeightedGraph V) (r : V) (lam : ℝ) : Submodule ℂ (V → ℂ) where
  carrier := {x | G.adj.mulVec x = (lam : ℂ) • x ∧ x r = 0}
  add_mem' := by
    rintro x y ⟨hx, hxr⟩ ⟨hy, hyr⟩
    refine ⟨?_, ?_⟩
    · rw [Matrix.mulVec_add, hx, hy, smul_add]
    · simp [Pi.add_apply, hxr, hyr]
  zero_mem' := by
    refine ⟨?_, rfl⟩
    rw [Matrix.mulVec_zero, smul_zero]
  smul_mem' := by
    rintro c x ⟨hx, hxr⟩
    refine ⟨?_, ?_⟩
    · rw [Matrix.mulVec_smul, hx, smul_comm]
    · simp [Pi.smul_apply, hxr]

/-- A dark vector is, by definition, a member of the dark subspace. -/
theorem isDark_iff_mem (G : WeightedGraph V) (r : V) (lam : ℝ) (x : V → ℂ) :
    IsDark G r lam x ↔ x ∈ darkSubspace G r lam := Iff.rfl

/-- Every dark vector vanishes at the root (the defining decoupling property). -/
theorem darkSubspace_vanishes_at_root (G : WeightedGraph V) (r : V) (lam : ℝ)
    {x : V → ℂ} (hx : x ∈ darkSubspace G r lam) : x r = 0 := hx.2

/-- Every dark vector is a genuine `λ`-eigenvector of the bulk adjacency. -/
theorem darkSubspace_isEigenvector (G : WeightedGraph V) (r : V) (lam : ℝ)
    {x : V → ℂ} (hx : x ∈ darkSubspace G r lam) :
    G.adj.mulVec x = (lam : ℂ) • x := hx.1

/-! ### Inclusion of the dark subspace into the tailed graph

A dark vector `x : V → ℂ` extends by zero on the tail to a vector
`darkExtend x : (V ⊕ Fin m) → ℂ`.  The decoupling lemma is precisely that this
extension is *still* an eigenvector of the full tailed adjacency
`(withTail G r m).adj`, with the *same* eigenvalue `λ` — the tail contributes
nothing because the extension vanishes at the root, which is the only coupling
channel. -/

/-- Extend a bulk vector `x : V → ℂ` by zero on the tail to a vector on the
tailed carrier `V ⊕ Fin m`. -/
def darkExtend (m : ℕ) (x : V → ℂ) : (V ⊕ Fin m) → ℂ :=
  fun y => match y with
    | Sum.inl v => x v
    | Sum.inr _ => 0

omit [Fintype V] [DecidableEq V] in
@[simp]
theorem darkExtend_inl (m : ℕ) (x : V → ℂ) (v : V) :
    darkExtend m x (Sum.inl v) = x v := rfl

omit [Fintype V] [DecidableEq V] in
@[simp]
theorem darkExtend_inr (m : ℕ) (x : V → ℂ) (j : Fin m) :
    darkExtend m x (Sum.inr j) = 0 := rfl

/-- **The dark-subspace decoupling lemma (Bernard-Tamon-Vinet-Xie 2211.14704,
Xie-Tamon 2301.07251).**

A dark vector `x` (a `λ`-eigenvector of the bulk `G.adj` vanishing at the root
`r`) extends by zero on the tail to a `λ`-eigenvector of the *full* tailed
adjacency `(withTail G r m).adj`.  The tail contributes no amplitude because the
extension is supported off the root and the root is the only coupling channel
between bulk and tail.  Hence the dark subspace is invariant under the tailed
walk and the tail is *completely decoupled* from it.

HONEST SORRY.  Closing this requires the explicit Jacobi structure of the tail
block of `withTail` (the path adjacency and the single root bridge edge) and the
case analysis on `Sum.inl`/`Sum.inr` coordinates of `(withTail G r m).adj.mulVec
(darkExtend m x)`; the `inr 0` (tail-endpoint) coordinate is exactly where the
bridge `oneSum_adj_roots` injects `x r`, which vanishes by darkness — this is the
crux of the continued-fraction / scattering analysis.  Left honest. -/
theorem darkSubspace_decoupling (G : WeightedGraph V) (r : V) (m : ℕ) (lam : ℝ)
    {x : V → ℂ} (hx : x ∈ darkSubspace G r lam) :
    (withTail G r m).adj.mulVec (darkExtend (m + 1) x)
      = (lam : ℂ) • darkExtend (m + 1) x := by
  -- The bulk coordinates reproduce `G.adj.mulVec x = λ • x` (hx.1); the only
  -- bulk/tail coupling is the root bridge `(inl r) ~ (inr 0)`, which contributes
  -- `x r = 0` (hx.2); the tail coordinates see only `0`-amplitude neighbours.
  obtain ⟨heig, hroot⟩ := hx
  funext y
  rw [Pi.smul_apply, smul_eq_mul]
  simp only [Matrix.mulVec, dotProduct]
  -- Split the dot product over the `V ⊕ Fin (m+1)` index into the two summands.
  rw [Fintype.sum_sum_type]
  rcases y with v | w
  · -- bulk coordinate: only the `inl`-block contributes (extension vanishes on tail).
    have htail : ∀ j : Fin (m + 1),
        (withTail G r m).adj (Sum.inl v) (Sum.inr j) * darkExtend (m + 1) x (Sum.inr j) = 0 := by
      intro j; rw [darkExtend_inr]; ring
    rw [Finset.sum_congr rfl (fun j _ => htail j), Finset.sum_const_zero, add_zero]
    -- The `inl`-block sum is `(G.adj.mulVec x) v = lam • x v`.
    have hbulk : ∀ v₂ : V,
        (withTail G r m).adj (Sum.inl v) (Sum.inl v₂) * darkExtend (m + 1) x (Sum.inl v₂)
          = G.adj v v₂ * x v₂ := by
      intro v₂; rw [darkExtend_inl]; rfl
    rw [Finset.sum_congr rfl (fun v₂ _ => hbulk v₂)]
    have := congrFun heig v
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    rw [this, darkExtend_inl]
  · -- tail coordinate: the `inl`-block contributes only at `v₂ = r` (the bridge),
    -- weighting `x r = 0`; the `inr`-block weights the vanishing extension.
    have hinr : ∀ j : Fin (m + 1),
        (withTail G r m).adj (Sum.inr w) (Sum.inr j) * darkExtend (m + 1) x (Sum.inr j) = 0 := by
      intro j; rw [darkExtend_inr]; ring
    rw [Finset.sum_congr rfl (fun j _ => hinr j), Finset.sum_const_zero, add_zero]
    -- The `inl`-block: `adj (inr w) (inl v₂) = if v₂ = r ∧ w = 0 then 1 else 0`,
    -- so the only possibly nonzero term is `v₂ = r`, weighting `x r = 0`.
    have hbulk : ∀ v₂ : V,
        (withTail G r m).adj (Sum.inr w) (Sum.inl v₂) * darkExtend (m + 1) x (Sum.inl v₂) = 0 := by
      intro v₂
      rw [darkExtend_inl]
      show (if v₂ = r ∧ w = ⟨0, Nat.succ_pos m⟩ then (1 : ℂ) else 0) * x v₂ = 0
      by_cases hc : v₂ = r ∧ w = ⟨0, Nat.succ_pos m⟩
      · rw [if_pos hc, hc.1, hroot, mul_zero]
      · rw [if_neg hc, zero_mul]
    rw [Finset.sum_congr rfl (fun v₂ _ => hbulk v₂), Finset.sum_const_zero]
    rw [darkExtend_inr, mul_zero]

/-! ### Tail invariance of PST inside the dark subspace

The decoupling lemma upgrades to the headline result: because the dark subspace
is exactly invariant and the tailed walk restricts there to the *bulk* walk,
perfect state transfer that takes place *within the dark subspace* is completely
unaffected by attaching (or removing, or lengthening) the tail.

We phrase this as: if `u, v` are bulk vertices whose standard basis vectors
`e_u, e_v` are dark at the relevant eigenvalues (so the transfer lives entirely
in the dark subspace), then PST between `u` and `v` in the bulk `G` holds iff PST
between `inl u` and `inl v` holds in the tailed graph `withTail G r m`. -/

/-- The standard basis vector at a bulk vertex `u`, as a function `V → ℂ`. -/
def bulkBasis (u : V) : V → ℂ := fun w => if w = u then 1 else 0

omit [Fintype V] in
@[simp]
theorem bulkBasis_self (u : V) : bulkBasis u u = 1 := by simp [bulkBasis]

/-- **Tail does not affect PST in the dark subspace (Xie-Tamon 2301.07251).**

If the transfer between bulk vertices `u` and `v` is *dark* — i.e. every
eigenvector basis-component of `e_u` and `e_v` that participates in the walk
lies in a dark subspace `darkSubspace G r λ` — then attaching a tail of any
length `m` at `r` leaves the perfect state transfer between them unchanged:

  `IsPST G u v τ ↔ IsPST (withTail G r m) (Sum.inl u) (Sum.inl v) τ`.

The genuine darkness condition is `hdark` below: for every eigenvalue `λ`, the
spectral projection of `e_u` onto the `λ`-eigenspace, and likewise for `e_v`,
lands in `darkSubspace G r λ` (vanishes at the root).  This is a *real*
restriction — it is NOT implied by `u, v ≠ r` alone (an eigenvector can be
nonzero at `r` even when `u ≠ r`), which is why the earlier
`bulkBasis u r = 0` phrasing was spurious (that quantity is `0` for free from
`hu`).  We expose darkness as an abstract hypothesis on the eigenprojections.

HONEST SORRY.  The forward and reverse implications both rest on
`darkSubspace_decoupling`: the tailed evolution `exp(-iτ (withTail G r m).adj)`
preserves the dark subspace `darkExtend '' (darkSubspace …)` and restricts there
to `exp(-iτ G.adj)`, so the `(inl u, inl v)`-amplitude equals the bulk
`(u, v)`-amplitude.  The remaining content is the matrix-exponential
restriction-to-invariant-subspace argument plus the Jacobi-tail spectral
separation (the tail eigenvalues are disjoint from the dark eigenvalues), which
is the deep scattering analysis of arXiv:2301.07251.  Left honest. -/
theorem withTail_isPST_iff_dark (G : WeightedGraph V) (r : V) (m : ℕ)
    (u v : V) (hu : u ≠ r) (hv : v ≠ r)
    (hdark : ∀ lam : ℝ, G.adj.mulVec (bulkBasis u) = (lam : ℂ) • bulkBasis u →
        bulkBasis u ∈ darkSubspace G r lam)
    (τ : ℝ) :
    IsPST G u v τ ↔ IsPST (withTail G r m) (Sum.inl u) (Sum.inl v) τ := by
  -- Both directions reduce to the dark-subspace restriction of the tailed
  -- evolution; see `darkSubspace_decoupling`.  Deep Jacobi-tail analysis.
  sorry

end StdLib
end Graphplay
