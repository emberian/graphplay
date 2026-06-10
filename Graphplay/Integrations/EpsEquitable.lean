/-
# Graphplay.Integrations.EpsEquitable

**ε-equitable attention, phase 0**: the approximate counterpart of the exact
block-equitable collapse.  `AttentionComplexity` proves that *exactly*
cell-constant attention (`A i j = B (cell i) (cell j)`) admits a linear-in-`n`
apply with zero error; real learned attention is only *approximately*
cell-constant.  This module supplies the definitions and the first theorems
that control what the linear algorithm costs in *accuracy* when the structure
holds only up to `ε`:

1. **`IsEpsBlock`** — `A` is within `ε` (entrywise) of the block matrix
   `equitablePart B cell`; `ε = 0` recovers the exact `hblock` hypothesis
   (`isEpsBlock_zero_iff`, matching `residual_eq_zero_iff_block`).
2. **`blockApply_approximates_fullApply`** — the `O(n·r·d)` block apply tracks
   the dense `O(n²·d)` apply to within `ε · ∑ⱼ |V j e|` per output coordinate.
   The error of the *fast algorithm on the learned matrix* is controlled by the
   *structural defect* `ε`, uniformly in `n`'s quadratic blow-up.
3. **`cellAverage_minimizes_residual`** — the cell-pair mean `cellAverage A cell`
   is the **orthogonal projection** of `A` onto the subspace of block matrices:
   among all `B`, it minimizes `frobNormSq (residual A B cell)`.  Per fiber this
   is the complete-the-square identity `∑(x−b)² = ∑(x−μ)² + m(μ−b)²`, the same
   least-squares mechanism as Eckart–Young (Eckart–Young, *Psychometrika* 1936),
   here for the block-constant subspace instead of the low-rank variety.
4. **`blockOsc`** — the within-block oscillation of `A`: the largest entry
   difference over index pairs lying in the same cell pair.  It moves by at most
   `|η| · blockOsc gradA` under one gradient step (`blockOsc_gradient_step`), and
   it **brackets the optimal `ε` within a factor 2**
   (`cellAverage_eps_bracket`): `cellAverage` achieves `ε = blockOsc A cell`,
   while *no* `B` can achieve better than `blockOsc A cell / 2`.  So tracking the
   single scalar `blockOsc` along training tracks the best achievable
   approximation quality of the linear algorithm, up to a factor 2.
5. **`blockGrad_eq_card_smul_cellAverage`** — the tied-weight backward pass of
   `AttentionComplexity.blockGrad` *is* the projected gradient: the block
   gradient at `(c, c')` equals `|C_c| · |C_c'| · cellAverage gradA cell c c'`.
   Training the `r × r` block parameters by cell aggregation is gradient descent
   along the orthogonal projection of the dense gradient onto the block subspace.

Why the hypotheses are what they are.  `IsEpsBlock` must be *entrywise*: a
Frobenius-level `ε` would let a single huge entry hide in a long sequence and
break the per-coordinate apply bound (take `A = equitablePart B cell` except
`A 0 0 += n`, `V` the indicator of token `0`).  The bracket factor 2 is real:
on one cell with entries `{0, ε}` the best block constant is `ε/2`
(`IsEpsBlock` with `ε/2`) while `blockOsc = ε`.

Empty cells: `cellAverage` is `0` on cell pairs with an empty fiber (ℝ-division
by zero), which is also the least-squares-correct value — the fiber contributes
nothing to the residual, and every theorem below holds with no surjectivity
hypothesis on `cell`.

## References

* Eckart, Young, "The approximation of one matrix by another of lower rank",
  *Psychometrika* 1 (1936) — least-squares projection mechanism.
* Cardoso, Delorme, Rama, "Laplacian eigenvectors and eigenvalues and almost
  equitable partitions", *European J. Combin.* 28 (2007) — almost/approximately
  equitable partitions.
* Vaswani et al., *Attention Is All You Need*, NeurIPS 2017.
* `Graphplay.Integrations.AttentionComplexity` (exact collapse),
  `Graphplay.Integrations.EquitableMechanism` (residual, `frobNormSq`),
  `Graphplay.Equitable` (exact `EquitablePartition`).
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Fold
import Graphplay.Equitable
import Graphplay.Integrations.AttentionComplexity
import Graphplay.Integrations.EquitableMechanism

open scoped BigOperators

namespace Graphplay
namespace EpsEquitable

open AttentionComplexity EquitableMechanism

variable {n r d : ℕ}

/-! ## §0. Definitions -/

/-- **`A` is an `ε`-block matrix** for the labelling `cell` and block values `B`:
every entry of `A` is within `ε` of its block value.  `ε = 0` is exactly the
`hblock` hypothesis of `blockAttentionApply_eq_fullAttentionApply`
(`isEpsBlock_zero_iff`).  The condition is entrywise (`L∞` on the residual), not
Frobenius: an averaged bound would let one large entry hide in a long sequence
and destroy the per-coordinate apply bound of §1. -/
def IsEpsBlock (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin r) (Fin r) ℝ)
    (cell : Fin n → Fin r) (ε : ℝ) : Prop :=
  ∀ i j, |A i j - B (cell i) (cell j)| ≤ ε

/-- An **ε-equitable partition** of a real (score) matrix `A`: a cell labelling
under which any two tokens of the same cell have per-cell branching sums (row
mass into each cell) within `ε` of each other.  The `ε = 0` instance is the
weighted-graph `EquitablePartition.uniform` condition of `Graphplay.Equitable`,
specialized to real entries. -/
structure EpsEquitablePartition (A : Matrix (Fin n) (Fin n) ℝ) (r : ℕ) (ε : ℝ) where
  /-- The cell labelling. -/
  cells : Fin n → Fin r
  /-- Approximate branching: tokens in the same cell see each cell with the same
  total mass, up to `ε`. -/
  uniform_approx : ∀ (j : Fin r) (x y : Fin n), cells x = cells y →
    |(∑ z, if cells z = j then A x z else 0)
      - (∑ z, if cells z = j then A y z else 0)| ≤ ε

/-- The **fiber** of cell `c`: the tokens labelled `c`. -/
def fiber (cell : Fin n → Fin r) (c : Fin r) : Finset (Fin n) :=
  Finset.univ.filter (fun i => cell i = c)

@[simp] theorem mem_fiber {cell : Fin n → Fin r} {c : Fin r} {i : Fin n} :
    i ∈ fiber cell c ↔ cell i = c := by
  simp [fiber]

/-- The number of tokens in cell `c`. -/
def fiberCard (cell : Fin n → Fin r) (c : Fin r) : ℕ := (fiber cell c).card

/-- The **cell-pair average** of `A`: the mean of the entries over the fiber pair
`C_c × C_c'`.  This is the orthogonal projection of `A` onto the block-matrix
subspace (`cellAverage_minimizes_residual`).  On a cell pair with an empty fiber
the ℝ-convention `x / 0 = 0` gives the entry `0` — the least-squares-correct
value, since empty fibers contribute nothing to the residual. -/
noncomputable def cellAverage (A : Matrix (Fin n) (Fin n) ℝ) (cell : Fin n → Fin r) :
    Matrix (Fin r) (Fin r) ℝ :=
  fun c c' => (∑ p ∈ fiber cell c ×ˢ fiber cell c', A p.1 p.2)
    / ((fiber cell c ×ˢ fiber cell c').card : ℝ)

/-- `cellAverage` in double-sum form: the entry sum over the fiber pair divided
by the product of the fiber sizes. -/
theorem cellAverage_eq (A : Matrix (Fin n) (Fin n) ℝ) (cell : Fin n → Fin r)
    (c c' : Fin r) :
    cellAverage A cell c c'
      = (∑ i ∈ fiber cell c, ∑ j ∈ fiber cell c', A i j)
        / ((fiberCard cell c : ℝ) * (fiberCard cell c' : ℝ)) := by
  unfold cellAverage fiberCard
  rw [Finset.sum_product, Finset.card_product]
  push_cast
  ring_nf

/-- `ε = 0` recovers the exact block hypothesis of
`blockAttentionApply_eq_fullAttentionApply`; together with
`residual_eq_zero_iff_block`, exact equitability = zero residual = zero `ε`. -/
theorem isEpsBlock_zero_iff (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin r) (Fin r) ℝ) (cell : Fin n → Fin r) :
    IsEpsBlock A B cell 0 ↔ ∀ i j, A i j = B (cell i) (cell j) := by
  unfold IsEpsBlock
  constructor
  · intro h i j
    exact sub_eq_zero.mp (abs_nonpos_iff.mp (h i j))
  · intro h i j
    rw [h i j, sub_self, abs_zero]

/-- An `ε`-block matrix is `2·ε·n`-equitable under the same cells: two tokens of
one cell route into each cell with sums differing by at most `2ε` per entry of
the (≤ `n`-element) target fiber.  This is the bridge from the entrywise defect
to the branching-sum (almost-equitable, Cardoso–Delorme–Rama) condition. -/
def IsEpsBlock.toEpsEquitable {A : Matrix (Fin n) (Fin n) ℝ}
    {B : Matrix (Fin r) (Fin r) ℝ} {cell : Fin n → Fin r} {ε : ℝ}
    (h : IsEpsBlock A B cell ε) : EpsEquitablePartition A r (2 * ε * n) where
  cells := cell
  uniform_approx := by
    intro j x y hxy
    have hε : 0 ≤ ε := le_trans (abs_nonneg _) (h x x)
    rw [← Finset.sum_sub_distrib]
    calc |∑ z, ((if cell z = j then A x z else 0) - (if cell z = j then A y z else 0))|
        ≤ ∑ z, |(if cell z = j then A x z else 0) - (if cell z = j then A y z else 0)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _z : Fin n, 2 * ε := by
          apply Finset.sum_le_sum
          intro z _
          by_cases hz : cell z = j
          · simp only [if_pos hz]
            calc |A x z - A y z|
                ≤ |A x z - B (cell x) (cell z)| + |B (cell x) (cell z) - A y z| :=
                  abs_sub_le _ _ _
              _ = |A x z - B (cell x) (cell z)| + |A y z - B (cell y) (cell z)| := by
                  rw [hxy, abs_sub_comm (B (cell y) (cell z)) (A y z)]
              _ ≤ ε + ε := add_le_add (h x z) (h y z)
              _ = 2 * ε := by ring
          · simp only [if_neg hz, sub_self, abs_zero]
            linarith
      _ = 2 * ε * n := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring

/-! ## §1. The approximate apply bound

The fast `O(n·r·d)` algorithm run on the block values `B` tracks the dense
`O(n²·d)` apply of the *learned* `A` to within `ε · ‖V‖₁` per output coordinate.
The entrywise hypothesis is necessary: the bound is per-coordinate, so a single
`Θ(n)` entry defect (invisible to averaged norms) would break it. -/

/-- **The block apply approximates the full apply (the `ε`-version of the exact
collapse).**  Under `IsEpsBlock A B cell ε`, every output coordinate of the
linear-time `blockAttentionApply B cell V` is within `ε · ∑ⱼ |V j e|` of the
dense `fullAttentionApply A V`.  Route: the block apply *equals* the full apply
of `equitablePart B cell` (the exact theorem), so the error is the residual
`A − equitablePart B cell` contracted against `V` — `n` terms, each `≤ ε·|V j e|`.
The error budget scales with the value mass, not with `n²`. -/
theorem blockApply_approximates_fullApply
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin r) (Fin r) ℝ)
    (cell : Fin n → Fin r) (V : Fin n → Fin d → ℝ) {ε : ℝ}
    (h : IsEpsBlock A B cell ε) (i : Fin n) (e : Fin d) :
    |fullAttentionApply A V i e - blockAttentionApply B cell V i e|
      ≤ ε * ∑ j, |V j e| := by
  have hb : blockAttentionApply B cell V = fullAttentionApply (equitablePart B cell) V :=
    blockAttentionApply_eq_fullAttentionApply (equitablePart B cell) B cell V
      (fun _ _ => rfl)
  rw [hb]
  have hdiff : fullAttentionApply A V i e
      - fullAttentionApply (equitablePart B cell) V i e
      = ∑ j, (A i j - B (cell i) (cell j)) * V j e := by
    unfold fullAttentionApply equitablePart
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hdiff]
  calc |∑ j, (A i j - B (cell i) (cell j)) * V j e|
      ≤ ∑ j, |(A i j - B (cell i) (cell j)) * V j e| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |A i j - B (cell i) (cell j)| * |V j e| := by
        exact Finset.sum_congr rfl fun j _ => abs_mul _ _
    _ ≤ ∑ j, ε * |V j e| := Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_right (h i j) (abs_nonneg _)
    _ = ε * ∑ j, |V j e| := by rw [Finset.mul_sum]

/-! ## §2. `cellAverage` is the orthogonal projection onto block matrices

The block matrices `equitablePart B cell` form a linear subspace of
`Matrix (Fin n) (Fin n) ℝ`, and the Frobenius-nearest point of that subspace to
`A` is the cell-pair mean.  Per fiber this is the one-dimensional least-squares
fact `∑(x−b)² = ∑(x−μ)² + m·(μ−b)² ≥ ∑(x−μ)²` — the cross term vanishes because
`μ` is the mean. -/

/-- **Complete the square.**  Over any finite index set, the mean minimizes the
sum of squared deviations: `∑ (f x − μ)² ≤ ∑ (f x − b)²` for every `b`, where
`μ = (∑ f) / |s|`.  (Empty `s`: both sides are `0`.)  The identity behind it is
`∑(f−b)² = ∑(f−μ)² + |s|·(μ−b)²`, whose cross term `2(μ−b)·∑(f−μ)` dies because
`∑ f = |s|·μ`. -/
theorem sum_sq_sub_mean_le {α : Type*} (s : Finset α) (f : α → ℝ) (b : ℝ) :
    ∑ x ∈ s, (f x - (∑ y ∈ s, f y) / (s.card : ℝ)) ^ 2
      ≤ ∑ x ∈ s, (f x - b) ^ 2 := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  · set μ : ℝ := (∑ y ∈ s, f y) / (s.card : ℝ) with hμ
    have hcard : (s.card : ℝ) ≠ 0 := by
      exact_mod_cast Finset.card_ne_zero.mpr hs
    have hsum0 : ∑ x ∈ s, (f x - μ) = 0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hμ,
        mul_comm ((s.card : ℝ)), div_mul_cancel₀ _ hcard, sub_self]
    have hkey : ∑ x ∈ s, (f x - b) ^ 2
        = ∑ x ∈ s, (f x - μ) ^ 2 + (s.card : ℝ) * (μ - b) ^ 2 := by
      have hexp : ∑ x ∈ s, (f x - b) ^ 2
          = ∑ x ∈ s, ((f x - μ) ^ 2 + 2 * (μ - b) * (f x - μ) + (μ - b) ^ 2) :=
        Finset.sum_congr rfl fun x _ => by ring
      rw [hexp, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
        hsum0, mul_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    rw [hkey]
    exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))

/-- The Frobenius² residual regrouped over cell-pair fibers:
`‖A − equitablePart B cell‖_F² = ∑_{c,c'} ∑_{(i,j) ∈ C_c × C_c'} (A i j − B c c')²`.
On each fiber the block value is the *single constant* `B c c'` — this is what
makes the per-fiber least-squares lemma applicable. -/
theorem frobNormSq_residual_eq_fiber_sum (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin r) (Fin r) ℝ) (cell : Fin n → Fin r) :
    frobNormSq (EquitableMechanism.residual A B cell)
      = ∑ c : Fin r, ∑ c' : Fin r,
          ∑ p ∈ fiber cell c ×ˢ fiber cell c', (A p.1 p.2 - B c c') ^ 2 := by
  have h1 : frobNormSq (EquitableMechanism.residual A B cell)
      = ∑ p : Fin n × Fin n, (A p.1 p.2 - B (cell p.1) (cell p.2)) ^ 2 := by
    unfold frobNormSq EquitableMechanism.residual equitablePart
    rw [← Finset.sum_product', Finset.univ_product_univ]
    exact Finset.sum_congr rfl fun p _ => by rw [Matrix.sub_apply]
  rw [h1,
    ← Finset.sum_fiberwise Finset.univ (fun p : Fin n × Fin n => (cell p.1, cell p.2))
      (fun p => (A p.1 p.2 - B (cell p.1) (cell p.2)) ^ 2),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => ?_
  have hset : Finset.univ.filter
        (fun p : Fin n × Fin n => (cell p.1, cell p.2) = (c, c'))
      = fiber cell c ×ˢ fiber cell c' := by
    ext p
    simp [fiber, Finset.mem_product, Prod.ext_iff]
  rw [hset]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mem_product] at hp
  rw [mem_fiber.mp hp.1, mem_fiber.mp hp.2]

/-- **`cellAverage` minimizes the residual (orthogonal projection onto the block
subspace).**  For every block matrix `B`,
`‖A − equitablePart (cellAverage A cell) cell‖_F² ≤ ‖A − equitablePart B cell‖_F²`.
Cell-averaging the *learned* `A` is the Frobenius-optimal block compression —
the precise sense in which `cellAverage` is the right `B` to hand to the linear
algorithm of §1.  Fiberwise it is `sum_sq_sub_mean_le`; the empty-fiber entries
of `cellAverage` (= `0`) never appear in the residual. -/
theorem cellAverage_minimizes_residual (A : Matrix (Fin n) (Fin n) ℝ)
    (cell : Fin n → Fin r) (B : Matrix (Fin r) (Fin r) ℝ) :
    frobNormSq (EquitableMechanism.residual A (cellAverage A cell) cell)
      ≤ frobNormSq (EquitableMechanism.residual A B cell) := by
  rw [frobNormSq_residual_eq_fiber_sum, frobNormSq_residual_eq_fiber_sum]
  refine Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun c' _ => ?_
  exact sum_sq_sub_mean_le (fiber cell c ×ˢ fiber cell c')
    (fun p => A p.1 p.2) (B c c')

/-! ## §3. Block oscillation: the trainable scalar that brackets the optimal `ε`

`blockOsc A cell` is the largest within-block entry difference.  It is (a)
computable from `A` alone — no candidate `B` needed, (b) Lipschitz along
gradient steps, and (c) a 2-approximation of the optimal `IsEpsBlock` epsilon,
witnessed by `cellAverage`. -/

/-- The **block oscillation** of `A` under `cell`: the maximum of
`|A i j − A i' j'|` over index pairs in the same cell pair
(`cell i = cell i'`, `cell j = cell j'`), `0`-defaulted (so `blockOsc = 0` when
`n = 0`, and always `≥ 0` since `(i,j)` vs itself contributes `0`). -/
def blockOsc (A : Matrix (Fin n) (Fin n) ℝ) (cell : Fin n → Fin r) : ℝ :=
  Finset.univ.fold max 0
    (fun q : (Fin n × Fin n) × Fin n × Fin n =>
      if cell q.1.1 = cell q.2.1 ∧ cell q.1.2 = cell q.2.2
        then |A q.1.1 q.1.2 - A q.2.1 q.2.2| else 0)

theorem blockOsc_nonneg (A : Matrix (Fin n) (Fin n) ℝ) (cell : Fin n → Fin r) :
    0 ≤ blockOsc A cell := by
  unfold blockOsc
  rw [Finset.le_fold_max]
  exact Or.inl le_rfl

/-- Any within-block entry difference is at most the block oscillation. -/
theorem abs_sub_le_blockOsc (A : Matrix (Fin n) (Fin n) ℝ) (cell : Fin n → Fin r)
    {i j i' j' : Fin n} (h1 : cell i = cell i') (h2 : cell j = cell j') :
    |A i j - A i' j'| ≤ blockOsc A cell := by
  unfold blockOsc
  rw [Finset.le_fold_max]
  exact Or.inr ⟨((i, j), (i', j')), Finset.mem_univ _,
    le_of_eq (if_pos ⟨h1, h2⟩).symm⟩

/-- `blockOsc` is the *least* such bound: any nonnegative `c` dominating all
within-block differences dominates `blockOsc`. -/
theorem blockOsc_le (A : Matrix (Fin n) (Fin n) ℝ) (cell : Fin n → Fin r) {c : ℝ}
    (hc : 0 ≤ c)
    (h : ∀ i j i' j', cell i = cell i' → cell j = cell j' →
      |A i j - A i' j'| ≤ c) :
    blockOsc A cell ≤ c := by
  unfold blockOsc
  rw [Finset.fold_max_le]
  refine ⟨hc, fun q _ => ?_⟩
  split_ifs with hq
  · exact h _ _ _ _ hq.1 hq.2
  · exact hc

/-- **One gradient step moves the block oscillation by at most
`|η| · blockOsc gradA cell`.**  So if the gradient itself is nearly
block-structured (small `blockOsc gradA cell`), approximate equitability of the
learned `A` is *stable* under training — the quantitative seed of the
"structure persists along SGD" half of the ε-equitable program.  Triangle
inequality per quadruple; no smoothness needed. -/
theorem blockOsc_gradient_step (A gradA : Matrix (Fin n) (Fin n) ℝ)
    (cell : Fin n → Fin r) (η : ℝ) :
    blockOsc (A - η • gradA) cell
      ≤ blockOsc A cell + |η| * blockOsc gradA cell := by
  apply blockOsc_le
  · exact add_nonneg (blockOsc_nonneg A cell)
      (mul_nonneg (abs_nonneg η) (blockOsc_nonneg gradA cell))
  · intro i j i' j' h1 h2
    have hentry : (A - η • gradA) i j - (A - η • gradA) i' j'
        = (A i j - A i' j') + -(η * (gradA i j - gradA i' j')) := by
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    rw [hentry]
    calc |(A i j - A i' j') + -(η * (gradA i j - gradA i' j'))|
        ≤ |A i j - A i' j'| + |-(η * (gradA i j - gradA i' j'))| := abs_add_le _ _
      _ = |A i j - A i' j'| + |η| * |gradA i j - gradA i' j'| := by
          rw [abs_neg, abs_mul]
      _ ≤ blockOsc A cell + |η| * blockOsc gradA cell :=
          add_le_add (abs_sub_le_blockOsc A cell h1 h2)
            (mul_le_mul_of_nonneg_left (abs_sub_le_blockOsc gradA cell h1 h2)
              (abs_nonneg η))

/-- The mean of values all within `ε` of `x` is within `ε` of `x`
(nonempty index set). -/
theorem abs_sub_mean_le {α : Type*} (s : Finset α) (hs : s.Nonempty) (f : α → ℝ)
    (x ε : ℝ) (h : ∀ y ∈ s, |x - f y| ≤ ε) :
    |x - (∑ y ∈ s, f y) / (s.card : ℝ)| ≤ ε := by
  have hcard : (0 : ℝ) < (s.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hs
  have h1 : x - (∑ y ∈ s, f y) / (s.card : ℝ)
      = (∑ y ∈ s, (x - f y)) / (s.card : ℝ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, sub_div,
      mul_div_cancel_left₀ _ hcard.ne']
  rw [h1, abs_div, abs_of_pos hcard, div_le_iff₀ hcard]
  calc |∑ y ∈ s, (x - f y)| ≤ ∑ y ∈ s, |x - f y| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _y ∈ s, ε := Finset.sum_le_sum h
    _ = ε * (s.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- **`cellAverage` achieves `ε = blockOsc A cell`.**  Each entry `A i j` is
within the block oscillation of every entry in its fiber pair, hence of their
mean.  The fiber pair of `(cell i, cell j)` is nonempty — it contains `(i, j)` —
so no empty-fiber default is ever consulted. -/
theorem isEpsBlock_cellAverage (A : Matrix (Fin n) (Fin n) ℝ)
    (cell : Fin n → Fin r) :
    IsEpsBlock A (cellAverage A cell) cell (blockOsc A cell) := by
  intro i j
  unfold cellAverage
  apply abs_sub_mean_le _ ⟨(i, j), by simp [Finset.mem_product]⟩
  intro p hp
  rw [Finset.mem_product] at hp
  exact abs_sub_le_blockOsc A cell (mem_fiber.mp hp.1).symm (mem_fiber.mp hp.2).symm

/-- **No `B` beats half the block oscillation.**  If `IsEpsBlock A B cell ε`,
two same-block entries are both within `ε` of the *same* block value, so their
difference is at most `2ε` — hence `blockOsc A cell ≤ 2ε`.  (`0 ≤ ε` is needed
only for `n = 0`, where `blockOsc = 0` but the vacuous `IsEpsBlock` admits
negative `ε`.) -/
theorem blockOsc_le_two_mul (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin r) (Fin r) ℝ) (cell : Fin n → Fin r) {ε : ℝ} (hε : 0 ≤ ε)
    (h : IsEpsBlock A B cell ε) :
    blockOsc A cell ≤ 2 * ε := by
  apply blockOsc_le A cell (by linarith)
  intro i j i' j' h1 h2
  calc |A i j - A i' j'|
      ≤ |A i j - B (cell i) (cell j)| + |B (cell i) (cell j) - A i' j'| :=
        abs_sub_le _ _ _
    _ = |A i j - B (cell i) (cell j)| + |A i' j' - B (cell i') (cell j')| := by
        rw [h1, h2, abs_sub_comm (B (cell i') (cell j')) (A i' j')]
    _ ≤ ε + ε := add_le_add (h i j) (h i' j')
    _ = 2 * ε := by ring

/-- **The factor-2 bracket.**  `cellAverage` realizes `ε = blockOsc A cell`,
and every achievable `ε` satisfies `blockOsc A cell ≤ 2ε` — so the `ε` achieved
by cell-averaging is within a factor 2 of the optimum over all block matrices.
The factor is tight: one cell with entries `{0, δ}` has `blockOsc = δ` but
admits the block constant `δ/2` with `ε = δ/2`. -/
theorem cellAverage_eps_bracket (A : Matrix (Fin n) (Fin n) ℝ)
    (cell : Fin n → Fin r) :
    IsEpsBlock A (cellAverage A cell) cell (blockOsc A cell) ∧
    ∀ (B : Matrix (Fin r) (Fin r) ℝ) (ε : ℝ), 0 ≤ ε → IsEpsBlock A B cell ε →
      blockOsc A cell ≤ 2 * ε :=
  ⟨isEpsBlock_cellAverage A cell,
   fun B ε hε h => blockOsc_le_two_mul A B cell hε h⟩

/-! ## §4. The tied-weight backward pass is the projected gradient

`AttentionComplexity.blockGrad` aggregates the dense upstream gradient
`∂L/∂A` over cell pairs — that is exactly `|C_c|·|C_c'|` times the cell-pair
mean, i.e. the (unnormalized) orthogonal projection of `§2` applied to the
gradient.  Training the `r × r` block parameters is gradient descent in the
block subspace. -/

/-- **`blockGrad` = fiber sizes × `cellAverage` of the gradient.**  The
cell-aggregated backward pass of `training_step_linear_under_equitable` is the
projected dense gradient: `blockGrad cell gradA c c' = |C_c| · |C_c'| ·
cellAverage gradA cell c c'`.  Both sides vanish on empty fiber pairs, so no
surjectivity of `cell` is needed. -/
theorem blockGrad_eq_card_smul_cellAverage (cell : Fin n → Fin r)
    (gradA : Matrix (Fin n) (Fin n) ℝ) (c c' : Fin r) :
    blockGrad cell (fun i j => gradA i j) c c'
      = (fiberCard cell c : ℝ) * (fiberCard cell c' : ℝ)
          * cellAverage gradA cell c c' := by
  have hlhs : blockGrad cell (fun i j => gradA i j) c c'
      = ∑ p ∈ fiber cell c ×ˢ fiber cell c', gradA p.1 p.2 := by
    unfold blockGrad
    rw [Finset.sum_product]
    have hsplit : ∀ i : Fin n,
        (∑ j, if cell i = c ∧ cell j = c' then gradA i j else 0)
          = if cell i = c then ∑ j ∈ fiber cell c', gradA i j else 0 := by
      intro i
      by_cases hi : cell i = c
      · rw [if_pos hi]
        unfold fiber
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hj : cell j = c'
        · rw [if_pos ⟨hi, hj⟩, if_pos hj]
        · rw [if_neg (fun hc => hj hc.2), if_neg hj]
      · rw [if_neg hi]
        exact Finset.sum_eq_zero fun j _ => if_neg (fun hc => hi hc.1)
    simp_rw [hsplit]
    rw [← Finset.sum_filter]
    rfl
  rw [hlhs]
  unfold cellAverage fiberCard
  rw [Finset.card_product]
  push_cast
  by_cases hz : ((fiber cell c).card : ℝ) * ((fiber cell c').card : ℝ) = 0
  · -- an empty fiber: the product finset is empty, both sides are 0.
    have hzn : (fiber cell c).card * (fiber cell c').card = 0 := by exact_mod_cast hz
    have hempty : fiber cell c ×ˢ fiber cell c' = ∅ :=
      Finset.card_eq_zero.mp (by rw [Finset.card_product]; exact hzn)
    rw [hempty]
    simp
  · obtain ⟨ha, hb⟩ := mul_ne_zero_iff.mp hz
    field_simp

end EpsEquitable
end Graphplay
