/-
# Graphplay.Tactics

**Reusable proof-automation for the Graphplay quantum-walk / PST corpus.**

This is a leaf utility module: it imports the settled foundations
(`Weighted`, `Equitable`, `Spectral`, `PST`, `Loopy`, `Product`) and Mathlib
basics, and exports

* a backbone of fully-proved **helper lemmas** for the recurring obligations,
* three **named simp sets** (`graphplay_herm`, `graphplay_modulus`,
  `graphplay_equitable`),
* an **aesop rule set** `Graphplay` seeded for Hermitian / membership goals,
* **custom tactics** `herm_grind`, `modulus_one`, `equitable_discharge`,
  `loopless_grind`,

together with `example`s demonstrating each tactic end-to-end.

------------------------------------------------------------------------------
## HOW TO USE (cheat-sheet for the next agents)

### (c) Hermitian goals — `herm_grind`
For a `WeightedGraph.herm` / `LoopyWeightedGraph.herm` field, or any goal
`M.IsHermitian` where `M` is built from entrywise `ite`s, sums, products,
diagonals, Kroneckers of Hermitian pieces:

    herm := by herm_grind

It reduces `IsHermitian` to the pointwise `star (M j i) = M i j` obligation,
then fires the `graphplay_herm` simp set (star pushed through `+`, `*`,
`ite`, real/nat casts, plus `G.herm.apply`).  For the *standalone* structural
combinators (`.add`, `.sub`, `.smul`, `.neg`, diagonal-of-real,
`B * Bᴴ`, `A ⊗ₖ B`) prefer the named helper lemmas
(`isHermitian_diagonal_ofReal`, `isHermitian_kronecker`, etc.) or
`aesop (rule_sets := [Graphplay])`.

### (b) Born-rule / unit-modulus goals — `modulus_one`
For `‖exp(-(I·τ·d))‖ = 1`, `‖Complex.exp (θ*I)‖ = 1`, `‖(c • M) j i‖`
phase factorings, `‖1‖`, products/conjugates of unit-modulus numbers:

    modulus_one

Backed by `norm_cexp_ofReal_mul_I`, `norm_cexp_real_smul_I`,
`norm_exp_neg_I_mul_three`, and `graphplay_modulus`.

### (a) Equitability `uniform` goals — `equitable_discharge`
For the `EquitablePartition.uniform` field
`∑ z, (if cells z = j then G.adj x z else 0) = ∑ z, (... y ...)`:

    uniform := by equitable_discharge <;> ...

It `intro`s the `i j x y hx hy` and tries to close with `P.uniform`,
`rfl`, congruence, or reduces to a same-cell sum congruence (see
`equitable_of_uniform_reindex`, `signed_cell_sum_factor`).

### Loopless goals — `loopless_grind`
For a `loopless` field `∀ v, adj v v = 0`:

    loopless := by loopless_grind

Intros the vertex and fires `graphplay_herm` + the looplessness of factors.

------------------------------------------------------------------------------
HARD CONSTRAINTS honoured here: no `axiom`/`admit`/`sorry` in any helper
lemma; no global `@[simp]` on foreign lemmas (only NAMED `graphplay_*`
attributes, applied to lemmas in this file or scoped onto Mathlib lemmas).
-/

import Graphplay.TacticsInit
import Graphplay.Weighted
import Graphplay.Equitable
import Graphplay.Spectral
import Graphplay.PST
import Graphplay.Loopy
import Graphplay.Product
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic

open scoped Matrix Kronecker
open NormedSpace

universe u v w

namespace Graphplay

/-! The named simp sets `graphplay_herm`, `graphplay_modulus`,
`graphplay_equitable` and the aesop rule set `Graphplay` are declared in the
companion leaf module `Graphplay.TacticsInit` (Lean cannot use a freshly
`register_simp_attr`/`declare_aesop_rule_sets` in its own declaring file).  We
populate them with our helper lemmas below. -/

/-! ============================================================================
## (c) HERMITIAN / LOOPLESS helper lemmas
============================================================================ -/

section Hermitian

variable {n : Type u} [DecidableEq n]

/-- A diagonal matrix whose entries are real-coerced complex numbers is
Hermitian.  This is the backbone of every Laplacian / degree-matrix `herm`
field. -/
theorem isHermitian_diagonal_ofReal (d : n → ℝ) :
    (Matrix.diagonal (fun i => (d i : ℂ))).IsHermitian := by
  apply Matrix.isHermitian_diagonal_iff.mpr
  intro i
  rw [isSelfAdjoint_iff, Complex.star_def, Complex.conj_ofReal]

/-- A diagonal matrix of self-adjoint (e.g. real) entries is Hermitian. -/
theorem isHermitian_diagonal_selfAdjoint {α : Type*} [CommRing α] [StarRing α]
    {m : Type*} [DecidableEq m] (d : m → α) (h : ∀ i, IsSelfAdjoint (d i)) :
    (Matrix.diagonal d).IsHermitian := by
  apply Matrix.isHermitian_diagonal_iff.mpr
  exact h

/-- The Kronecker product of two Hermitian matrices over `ℂ` is Hermitian.
The backbone of every `tensorProduct`-style `herm` field. -/
theorem isHermitian_kronecker {m : Type*} {p : Type*}
    {A : Matrix m m ℂ} {B : Matrix p p ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A ⊗ₖ B).IsHermitian := by
  show (A ⊗ₖ B)ᴴ = A ⊗ₖ B
  rw [Matrix.conjTranspose_kronecker, hA.eq, hB.eq]

/-- `B * Bᴴ` is always Hermitian (Gram matrix).  Used for Hodge / incidence
Laplacians. -/
theorem isHermitian_mul_conjTranspose {m : Type*} {p : Type*} [Fintype p]
    (B : Matrix m p ℂ) : (B * Bᴴ).IsHermitian :=
  Matrix.isHermitian_mul_conjTranspose_self B

/-- `Bᴴ * B` is always Hermitian. -/
theorem isHermitian_conjTranspose_mul {m : Type*} {p : Type*} [Fintype m]
    (B : Matrix m p ℂ) : (Bᴴ * B).IsHermitian :=
  Matrix.isHermitian_conjTranspose_mul_self B

/-- Masking the diagonal of a Hermitian matrix to `0` (the standard "make it
loopless" move) preserves Hermiticity, because the mask `(u = v)` is
symmetric.  Used for `hodgeLaplacian`-style `D - A`-off-diagonal
constructions. -/
theorem isHermitian_diagMask {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    (Matrix.of (fun u v => if u = v then 0 else M u v) : Matrix n n ℂ).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  show star (if j = i then 0 else M j i) = if i = j then 0 else M i j
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg h, if_neg (fun e => h e.symm)]; exact hM.apply i j

omit [DecidableEq n] in
/-- An entrywise-`ite` matrix whose `then` branches are Hermitian-symmetric and
whose guard is symmetric, is Hermitian.  Captures the
`if p = q then ... else 0` blocks in product / signed adjacencies. -/
theorem isHermitian_ite_symm {M : Matrix n n ℂ}
    (guard : n → n → Prop) [DecidableRel guard]
    (hsymm : ∀ i j, guard i j ↔ guard j i)
    (hstar : ∀ i j, guard i j → star (M j i) = M i j) :
    (Matrix.of (fun i j => if guard i j then M i j else 0) : Matrix n n ℂ).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  show star (if guard j i then M j i else 0) = if guard i j then M i j else 0
  by_cases h : guard i j
  · rw [if_pos h, if_pos ((hsymm i j).mp h), hstar i j h]
  · rw [if_neg h, if_neg (fun hc => h ((hsymm j i).mp hc)), star_zero]

end Hermitian

/-! ============================================================================
## (b) BORN-RULE / UNIT-MODULUS helper lemmas
============================================================================ -/

section Modulus

/-- `‖Complex.exp (θ • I)‖ = 1` for a real phase `θ`, in `ofReal`-coe form. -/
theorem norm_cexp_ofReal_mul_I (θ : ℝ) :
    ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I θ

/-- `‖Complex.exp (z)‖ = 1` whenever `z` is purely imaginary (`z.re = 0`). -/
theorem norm_cexp_eq_one_of_re_zero {z : ℂ} (hz : z.re = 0) :
    ‖Complex.exp z‖ = 1 := by
  rw [Complex.norm_exp, hz, Real.exp_zero]

/-- The CTQW global phase `e^{-(I·τ·d)}` with `τ, d` real has modulus one
(`NormedSpace.exp` form).  This is the entry-free engine behind every
diagonal-shift PST argument. -/
theorem norm_exp_neg_I_mul_three (τ d : ℝ) :
    ‖NormedSpace.exp (-(Complex.I * (τ : ℂ) * (d : ℂ)))‖ = 1 := by
  rw [← Complex.exp_eq_exp_ℂ]
  rw [show -(Complex.I * (τ : ℂ) * (d : ℂ)) = ((-(τ * d) : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- `‖Complex.exp (-(I·τ·d))‖ = 1` for real `τ, d`, in the bare `Complex.exp`
form (no `NormedSpace.exp`). -/
theorem norm_cexp_neg_I_mul (τ d : ℝ) :
    ‖Complex.exp (-(Complex.I * (τ : ℂ) * (d : ℂ)))‖ = 1 := by
  apply norm_cexp_eq_one_of_re_zero
  simp [Complex.mul_re, Complex.mul_im]

/-- Modulus of a scalar phase times a matrix entry: `‖(γ • M) j i‖ = ‖M j i‖`
when `‖γ‖ = 1`.  This is the entry-level form behind every
`norm_exp_shifted_entry_eq`-style diagonal-shift argument. -/
theorem norm_smul_entry_eq_of_norm_one {n : Type u} (γ : ℂ) (hγ : ‖γ‖ = 1)
    (M : Matrix n n ℂ) (i j : n) :
    ‖(γ • M) j i‖ = ‖M j i‖ := by
  rw [Matrix.smul_apply, norm_smul, hγ, one_mul]

/-- A product of two unit-modulus numbers is unit-modulus. -/
theorem norm_mul_eq_one {a b : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    ‖a * b‖ = 1 := by rw [norm_mul, ha, hb, one_mul]

/-- The conjugate of a unit-modulus number is unit-modulus. -/
theorem norm_star_eq_one {a : ℂ} (ha : ‖a‖ = 1) : ‖star a‖ = 1 := by
  rwa [norm_star]

/-- The inverse of a unit-modulus number is unit-modulus. -/
theorem norm_inv_eq_one {a : ℂ} (ha : ‖a‖ = 1) : ‖a⁻¹‖ = 1 := by
  rw [norm_inv, ha, inv_one]

end Modulus

/-! ============================================================================
## (a) EQUITABLE-PARTITION helper lemmas
============================================================================ -/

section Equitable

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : WeightedGraph V}
  {I : Type v} [Fintype I] [DecidableEq I]

/-- **Reindex an equitable uniform proof through an injective cell relabelling.**
If `cells = f ∘ cells'` with `f` injective, the uniform condition for `cells`
reduces to that of `cells'`.  Captures the `Sum.inl ∘ P.cells`,
`markedRefined`, product-relabelling, and graphon-coarsening `uniform` fields.

We phrase the conclusion as the raw `uniform`-shaped statement so it plugs
directly into an `EquitablePartition.uniform` field. -/
theorem uniform_of_comp_injective
    (P : EquitablePartition G I) {I' : Type w} [Fintype I'] [DecidableEq I']
    (f : I → I') (hf : Function.Injective f)
    (i' j' : I') (x y : V) (hx : f (P.cells x) = i') (hy : f (P.cells y) = i') :
    (∑ z, (if f (P.cells z) = j' then G.adj x z else 0))
      = (∑ z, (if f (P.cells z) = j' then G.adj y z else 0)) := by
  -- `P.cells x = P.cells y` since `f` is injective and both map to `i'`.
  have hxy : P.cells x = P.cells y := hf (hx.trans hy.symm)
  by_cases hj : ∃ j : I, f j = j'
  · obtain ⟨j, rfl⟩ := hj
    -- `f (cells z) = f j ↔ cells z = j` (injectivity of `f`).
    have key : ∀ (u : V),
        (∑ z, (if f (P.cells z) = f j then G.adj u z else 0))
          = (∑ z, (if P.cells z = j then G.adj u z else 0)) := by
      intro u
      refine Finset.sum_congr rfl (fun z _ => ?_)
      by_cases hz : P.cells z = j
      · rw [if_pos hz, if_pos (by rw [hz])]
      · rw [if_neg hz, if_neg (fun hc => hz (hf hc))]
    rw [key x, key y]
    exact P.uniform (P.cells x) j x y rfl hxy.symm
  · -- `j'` is not in the range of `f`: every guard is false, both sums vanish.
    simp only [not_exists] at hj
    have hzero : ∀ (u : V), (∑ z, (if f (P.cells z) = j' then G.adj u z else 0)) = 0 := by
      intro u
      refine Finset.sum_eq_zero (fun z _ => ?_)
      rw [if_neg (hj (P.cells z))]
    rw [hzero x, hzero y]

omit [Fintype I] in
/-- **Factor a cross-constant phase out of a signed cell sum.**  If a kernel
`σ x z = c` is constant (equal to `c`) for all `z` in cell `j` (when the
source `x` is in cell `i`), then the signed cell sum factors as `c` times the
unsigned cell sum.  This is the algebraic core of
`signedBy_preserves_equitable` and every chiral / magnetic `uniform` field. -/
theorem signed_cell_sum_factor (G : WeightedGraph V) (cells : V → I) (j : I)
    (x : V) (σ : V → V → ℂ) (c : ℂ) (hc : ∀ z, cells z = j → σ x z = c) :
    (∑ z, (if cells z = j then σ x z * G.adj x z else 0))
      = c * (∑ z, (if cells z = j then G.adj x z else 0)) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  by_cases hz : cells z = j
  · rw [if_pos hz, if_pos hz, hc z hz]
  · rw [if_neg hz, if_neg hz, mul_zero]

omit [Fintype I] in
/-- **Constant-degree ⇒ uniform.**  If for every vertex `x` and every cell `j`
the cell-sum equals a value depending only on `(cells x, j)`, the `uniform`
condition follows immediately.  A convenient packaging for graph constructions
whose branching numbers are given by an explicit closed form. -/
theorem uniform_of_branching_const (G : WeightedGraph V) (cells : V → I)
    (b : I → I → ℂ)
    (hb : ∀ (x : V) (j : I),
      (∑ z, (if cells z = j then G.adj x z else 0)) = b (cells x) j)
    (i j : I) (x y : V) (hx : cells x = i) (hy : cells y = i) :
    (∑ z, (if cells z = j then G.adj x z else 0))
      = (∑ z, (if cells z = j then G.adj y z else 0)) := by
  rw [hb x j, hb y j, hx, hy]

end Equitable

/-! ============================================================================
## SIMP-SET POPULATION

We scope safe rewrites into the named sets.  These `attribute` commands attach
the lemmas to the *named* set only — they do NOT register a global `@[simp]`.
============================================================================ -/

-- Hermitian set: star pushed through ring operations, casts, conjugation.
attribute [graphplay_herm]
  star_add star_mul' star_zero star_one star_neg star_sub
  Complex.conj_ofReal Complex.conj_natCast Complex.conj_I
  Matrix.conjTranspose_apply Matrix.add_apply Matrix.sub_apply
  Matrix.smul_apply

-- Modulus set: norm of phases / products / casts.
attribute [graphplay_modulus]
  norm_mul norm_star norm_inv norm_one
  Complex.norm_exp_ofReal_mul_I
  norm_cexp_ofReal_mul_I norm_exp_neg_I_mul_three norm_cexp_neg_I_mul

-- Equitable set: cell-sum / branching shape helpers.
attribute [graphplay_equitable]
  Finset.mul_sum Finset.sum_const mul_zero zero_mul

/-! ============================================================================
## AESOP RULE SET POPULATION

Seed the `Graphplay` aesop set with the Hermitian structural combinators and
the membership lemmas, so `aesop (rule_sets := [Graphplay])` can chain them.
============================================================================ -/

attribute [aesop safe apply (rule_sets := [Graphplay])]
  Matrix.IsHermitian.add Matrix.IsHermitian.sub Matrix.IsHermitian.neg
  isHermitian_diagonal_ofReal isHermitian_kronecker
  isHermitian_mul_conjTranspose isHermitian_conjTranspose_mul
  Submodule.add_mem Submodule.smul_mem Submodule.zero_mem

/-! ============================================================================
## CUSTOM TACTICS
============================================================================ -/

/-- **`herm_grind`** — discharge `Matrix.IsHermitian` / `herm`-field goals.

Strategy: try the structural helper lemmas / aesop set first (covers
`.add/.sub/.neg`, diagonal-of-real, Kronecker, Gram); otherwise reduce
`IsHermitian` to the pointwise `star (M j i) = M i j` obligation and grind the
`star`/`ite`/cast/`herm.apply` simp set, splitting on the `ite` guards. -/
syntax "herm_grind" : tactic
macro_rules
  | `(tactic| herm_grind) =>
    `(tactic|
      first
      | assumption
      | exact isHermitian_diagonal_ofReal _
      | (apply isHermitian_kronecker <;> assumption)
      | exact isHermitian_mul_conjTranspose _
      | exact isHermitian_conjTranspose_mul _
      | (apply Matrix.IsHermitian.add <;> assumption)
      | (apply Matrix.IsHermitian.sub <;> assumption)
      | (apply Matrix.IsHermitian.neg <;> assumption)
      | aesop (rule_sets := [Graphplay])
      | (refine Matrix.IsHermitian.ext ?_
         intro i j
         simp only [graphplay_herm]
         first
         | rfl
         | (split <;> simp_all [graphplay_herm] <;> ring_nf)
         | ring
         | (simp_all [graphplay_herm, Matrix.conjTranspose_apply]; done)))

/-- **`modulus_one`** — discharge unit-modulus / Born-rule goals `‖·‖ = 1`.

Tries the modulus simp set (covers products, conjugates, inverses, `exp`-phase
helpers) and the direct phase lemmas; falls back on reducing to a
`re = 0` exponent. -/
syntax "modulus_one" : tactic
macro_rules
  | `(tactic| modulus_one) =>
    `(tactic|
      first
      | assumption
      | (simp only [graphplay_modulus]; done)
      | (simp only [graphplay_modulus, Matrix.smul_apply, norm_smul] <;> simp_all [graphplay_modulus])
      | (simp_all only [graphplay_modulus]; done)
      | (apply norm_cexp_eq_one_of_re_zero
         simp [Complex.mul_re, Complex.mul_im])
      | (rw [Complex.norm_exp]; simp [Complex.mul_re, Complex.mul_im])
      | norm_num)

/-- **`loopless_grind`** — discharge a `loopless` field `∀ v, adj v v = 0`.

Intros the vertex and fires the looplessness of factors plus the `graphplay_herm`
shape simp set; handles `ite (v = v)` diagonal masks and Kronecker/product
zero-products. -/
syntax "loopless_grind" : tactic
macro_rules
  | `(tactic| loopless_grind) =>
    `(tactic|
      (intro v
       first
       | rfl
       | (simp only [Matrix.of_apply]; done)
       | (simp [Matrix.of_apply]; done)
       | (simp_all [Matrix.kronecker_apply, mul_eq_zero, Matrix.of_apply,
                    graphplay_herm]; done)
       | simp_all [Matrix.kronecker_apply, mul_eq_zero, graphplay_herm]))

/-- **`equitable_discharge`** — make progress on an `EquitablePartition.uniform`
goal `∀ i j x y, cells x = i → cells y = i → (∑ ...x...) = (∑ ...y...)`.

Intros the binders, then tries: closing by an upstream `P.uniform`, `rfl`,
congruence to a same-cell sum, or `simp` on the `graphplay_equitable` set.
Leaves a focused same-cell sum congruence when it cannot finish, which the
caller closes with the relevant `uniform_of_*` helper. -/
syntax "equitable_discharge" : tactic
macro_rules
  | `(tactic| equitable_discharge) =>
    `(tactic|
      (intro i j x y hx hy
       first
       | assumption
       | rfl
       | (subst_vars; rfl)
       | (simp only [graphplay_equitable]; try rfl)
       | (refine Finset.sum_congr rfl (fun z _ => ?_); simp_all [graphplay_equitable])
       | skip))

/-! ============================================================================
## VALIDATION EXAMPLES

Each example reproduces a real goal shape from the corpus and discharges it
with the corresponding tactic / helper, end-to-end (no `sorry`).
============================================================================ -/

section ValidationExamples

variable {V : Type u} [Fintype V] [DecidableEq V]
  {W : Type*} [Fintype W] [DecidableEq W]

/-- (c) `herm_grind` closes a diagonal-of-real `herm` goal (Laplacian shape). -/
example (d : V → ℝ) : (Matrix.diagonal (fun i => (d i : ℂ))).IsHermitian := by
  herm_grind

/-- (c) `herm_grind` closes the Kronecker-product `herm` field (tensorProduct
shape).  The factor Hermiticities are in context, as in the real `herm`
field. -/
example (G : WeightedGraph V) (H : WeightedGraph W) :
    (G.adj ⊗ₖ H.adj).IsHermitian := by
  have hG : G.adj.IsHermitian := G.herm
  have hH : H.adj.IsHermitian := H.herm
  herm_grind

/-- (c) `herm_grind` closes a `B * Bᴴ` Gram `herm` goal (hodgeLaplacian
shape). -/
example {p : Type*} [Fintype p] (B : Matrix V p ℂ) : (B * Bᴴ).IsHermitian := by
  herm_grind

/-- (c) `herm_grind` closes the `D - A` Laplacian `herm` goal (Loopy.laplacian
shape: real diagonal minus the Hermitian adjacency). -/
example (G : WeightedGraph V) :
    (Matrix.diagonal (fun v => ((G.degree v).re : ℂ)) - G.adj).IsHermitian := by
  have hd : (Matrix.diagonal (fun v => ((G.degree v).re : ℂ))).IsHermitian :=
    isHermitian_diagonal_ofReal _
  have ha : G.adj.IsHermitian := G.herm
  herm_grind

/-- (b) `modulus_one` closes the CTQW global-phase modulus (DiagonalShift /
Search shape). -/
example (τ d : ℝ) :
    ‖NormedSpace.exp (-(Complex.I * (τ : ℂ) * (d : ℂ)))‖ = 1 := by
  modulus_one

/-- (b) `modulus_one` closes a bare `Complex.exp` phase modulus
(LatticeGauge shape). -/
example (θ : ℝ) : ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := by
  modulus_one

/-- (b) `modulus_one` closes a product of unit-modulus phases (product-PST
`‖a‖·‖b‖ = 1` shape). -/
example (a b : ℂ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) : ‖a * b‖ = 1 := by
  modulus_one

/-- (c) `loopless_grind` closes a Kronecker-product loopless goal (the factor
looplessness is in context, as in the real `tensorProduct` field). -/
example (G : WeightedGraph V) (H : WeightedGraph W) :
    ∀ v : V × W, (G.adj ⊗ₖ H.adj) v v = 0 := by
  have hGl := G.loopless
  have hHl := H.loopless
  loopless_grind

/-- (c) `loopless_grind` closes a diagonal-mask loopless goal (hodgeLaplacian
shape). -/
example (M : Matrix V V ℂ) :
    ∀ v : V, (Matrix.of (fun u w => if u = w then 0 else M u w) : Matrix V V ℂ) v v = 0 := by
  loopless_grind

/-- (a) `equitable_discharge` closes a relabelled `uniform` field via the
discrete-partition `subst` route. -/
example (G : WeightedGraph V) :
    ∀ (i j : V) (x y : V), (id x = i) → (id y = i) →
      (∑ z, (if id z = j then G.adj x z else 0))
        = (∑ z, (if id z = j then G.adj y z else 0)) := by
  equitable_discharge

/-- (a) The `uniform_of_comp_injective` helper closes a `Sum.inl`-relabelled
partition `uniform` field (markedRefined shape). -/
example {I : Type v} [Fintype I] [DecidableEq I] (G : WeightedGraph V)
    (P : EquitablePartition G I) :
    ∀ (i j : I ⊕ Unit) (x y : V),
      (Sum.inl (P.cells x) = i) → (Sum.inl (P.cells y) = i) →
      (∑ z, (if Sum.inl (P.cells z) = j then G.adj x z else 0))
        = (∑ z, (if Sum.inl (P.cells z) = j then G.adj y z else 0)) := by
  intro i j x y hx hy
  exact uniform_of_comp_injective P Sum.inl (fun _ _ h => by simpa using h) i j x y hx hy

/-- (a) `signed_cell_sum_factor` factors a cross-constant phase out of a cell
sum (chiral `signedBy_preserves_equitable` core). -/
example (G : WeightedGraph V) (cells : V → V) (j : V) (x : V) (c : ℂ) :
    (∑ z, (if cells z = j then (fun _ _ => c) x z * G.adj x z else 0))
      = c * (∑ z, (if cells z = j then G.adj x z else 0)) := by
  exact signed_cell_sum_factor G cells j x (fun _ _ => c) c (fun _ _ => rfl)

end ValidationExamples

end Graphplay
