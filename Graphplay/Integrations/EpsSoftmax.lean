/-
# Graphplay.Integrations.EpsSoftmax

**Softmax and block structure** — closing the gap between the QK-transpose-level
structure that attention *probes* measure (the pre-softmax logit matrix `S`) and
the post-softmax attention operator that the rest of the library *consumes*
(`MachineLearning.AttentionMatrix`, a row-stochastic matrix).

The probe sees the logits `S i j` (or, in practice, an approximation of them).
The library consumes `softmaxRow S`, the row-wise softmax.  Three transfer
results bridge the two:

* **Block in ⇒ block out** (`softmaxRow_block_of_block`).  If the logits are a
  block matrix `S i j = T (cell i) (cell j)` — the exact symmetry a probe detects
  — then the *attention* `softmaxRow S` is the same shape of block matrix.  The
  row normalizer `∑_k exp(S i k) = ∑_c |fiber c|·exp(T (cell i) c)` depends only
  on the row's cell, so blockness survives softmax (the cell sizes enter the
  block *values* but not the *blockness*).

* **ε in ⇒ (exp 2ε − 1) out** (`softmaxRow_eps_of_eps`).  Softmax is Lipschitz in
  the sup norm of logits with the explicit modulus `exp(2ε) − 1`: an entrywise
  ε-perturbation of the logits moves each attention entry by at most
  `exp(2ε) − 1`.  The factor of `2` is sharp in this route — one ε from the
  numerator ratio, one from the row-sum ratio.

* **ε-block in ⇒ (exp 2ε − 1)-block out** (`softmaxRow_eps_block`), the
  composition: logits that are *approximately* block (within ε of an exact block
  matrix `T`) give attention that is approximately block with modulus
  `exp(2ε) − 1`.  This is the statement a real probe licenses: it never sees an
  exactly-block logit matrix, only an ε-block one.

Finally `softmaxAttention` packages `softmaxRow S` as a genuine
`MachineLearning.AttentionMatrix` (nonnegativity and row-stochasticity from the
softmax basics), feeding the equitable-partition machinery downstream.

## References

* Vaswani et al., *Attention Is All You Need*, NeurIPS 2017 (softmax attention).
-/

import Mathlib.Analysis.SpecialFunctions.Exp
import Graphplay.Integrations.MachineLearning

open scoped Matrix

namespace Graphplay
namespace EpsSoftmax

variable {n : ℕ}

/-! ## 1. Softmax basics: definition, positivity, row sums -/

/-- The **row normalizer** of the softmax: the partition function
`Z_i = ∑_k exp(S i k)` for row `i`.  Positive whenever the row index type is
inhabited (witnessed by the row `i` itself). -/
noncomputable def softmaxDenom (S : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : ℝ :=
  ∑ k, Real.exp (S i k)

/-- The **row-wise softmax** of a logit matrix `S`: `softmaxRow S i j` is the
attention weight from query `i` onto key `j`, `exp(S i j) / ∑_k exp(S i k)`.
This is the post-softmax operator the library consumes; `S` is the pre-softmax
(QK-transpose-level) logit matrix a probe measures. -/
noncomputable def softmaxRow (S : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => Real.exp (S i j) / ∑ k, Real.exp (S i k)

theorem softmaxRow_apply (S : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    softmaxRow S i j = Real.exp (S i j) / softmaxDenom S i := rfl

/-- The row normalizer is strictly positive: it is a sum of exponentials over a
nonempty index set (the row `i` witnesses nonemptiness). -/
theorem softmaxDenom_pos (S : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    0 < softmaxDenom S i :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) ⟨i, Finset.mem_univ i⟩

/-- Softmax entries are strictly positive. -/
theorem softmaxRow_pos (S : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    0 < softmaxRow S i j :=
  div_pos (Real.exp_pos _) (softmaxDenom_pos S i)

/-- Softmax entries are at most `1` (a single key's mass is at most the whole
row's mass). -/
theorem softmaxRow_le_one (S : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    softmaxRow S i j ≤ 1 := by
  rw [softmaxRow_apply, div_le_one (softmaxDenom_pos S i)]
  exact Finset.single_le_sum (fun k _ => (Real.exp_pos _).le) (Finset.mem_univ j)

/-- **Row-stochasticity.**  Each query's softmax row sums to `1`: it is a
probability distribution over keys. -/
theorem softmaxRow_rowSum (S : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    ∑ j, softmaxRow S i j = 1 := by
  simp only [softmaxRow_apply]
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (softmaxDenom_pos S i))

/-! ## 2. Block structure survives softmax -/

/-- **Block logits ⇒ block attention (PROVEN).**  If the logit matrix is constant
on cell-pairs, `S i j = T (cell i) (cell j)`, then the softmax attention matrix is
again constant on cell-pairs: `∃ T2, softmaxRow S i j = T2 (cell i) (cell j)`.

The mechanism: the row normalizer `∑_k exp(S i k) = ∑_k exp(T (cell i) (cell k))`
depends only on `cell i`, so the quotient `exp(T (cell i) (cell j)) / Z_{cell i}`
is itself a function of `(cell i, cell j)`.  Cell sizes enter the block *value*
(via the fiber-weighted normalizer) but not the *blockness*. -/
theorem softmaxRow_block_of_block (S : Matrix (Fin n) (Fin n) ℝ)
    {I : Type*} [Fintype I] [DecidableEq I]
    (cell : Fin n → I) (T : I → I → ℝ)
    (hblock : ∀ i j, S i j = T (cell i) (cell j)) :
    ∃ T2 : I → I → ℝ, ∀ i j, softmaxRow S i j = T2 (cell i) (cell j) := by
  refine ⟨fun a b => Real.exp (T a b) / (∑ k, Real.exp (T a (cell k))), fun i j => ?_⟩
  rw [softmaxRow_apply, softmaxDenom, hblock i j]
  congr 1
  exact Finset.sum_congr rfl (fun k _ => by rw [hblock i k])

/-! ## 3. Softmax is Lipschitz in the logits with modulus `exp(2ε) − 1` -/

/-- **One-sided softmax ratio bound (PROVEN).**  If the logits agree entrywise
within `ε`, then each softmax entry of `S` is bounded by `exp(2ε)` times the
corresponding entry of `S2`.  The factor `2`: one `ε` bounds the numerator ratio
`exp(S i j) / exp(S2 i j) ≤ exp ε`, one bounds the row-sum ratio
`Z_i^{S} / Z_i^{S2} ≤ exp ε`, and the softmax entry is the quotient of the two. -/
theorem softmaxRow_le_softmaxRow_mul (S S2 : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ)
    (hbound : ∀ a b, |S a b - S2 a b| ≤ ε) (i j : Fin n) :
    softmaxRow S i j ≤ softmaxRow S2 i j * Real.exp (2 * ε) := by
  have hee : Real.exp ε * Real.exp ε = Real.exp (2 * ε) := by
    rw [← Real.exp_add]; congr 1; ring
  -- numerator ratio: exp(S i j) ≤ exp(S2 i j)·exp ε
  have haj_le : Real.exp (S i j) ≤ Real.exp (S2 i j) * Real.exp ε := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp (hbound i j)).2])
  -- row-sum ratio: Z^{S2} ≤ Z^{S}·exp ε  (the comparison direction we need)
  have hBA : softmaxDenom S2 i ≤ softmaxDenom S i * Real.exp ε := by
    unfold softmaxDenom
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun k _ => by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp (hbound i k)).1])
  -- cross-multiplied inequality
  have key : Real.exp (S i j) * softmaxDenom S2 i
           ≤ Real.exp (S2 i j) * Real.exp (2 * ε) * softmaxDenom S i :=
    calc Real.exp (S i j) * softmaxDenom S2 i
        ≤ (Real.exp (S2 i j) * Real.exp ε) * (softmaxDenom S i * Real.exp ε) :=
          mul_le_mul haj_le hBA (softmaxDenom_pos S2 i).le
            (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
      _ = Real.exp (S2 i j) * Real.exp (2 * ε) * softmaxDenom S i := by rw [← hee]; ring
  rw [softmaxRow_apply, softmaxRow_apply, div_mul_eq_mul_div,
    div_le_div_iff₀ (softmaxDenom_pos S i) (softmaxDenom_pos S2 i)]
  exact key

/-- **Softmax is `exp(2ε) − 1`-Lipschitz in the sup norm of logits (PROVEN).**
If `|S i j − S2 i j| ≤ ε` entrywise (`0 ≤ ε`), then
`|softmaxRow S i j − softmaxRow S2 i j| ≤ exp(2ε) − 1`.

The two-sided ratio bound (`softmaxRow_le_softmaxRow_mul`, applied with `S, S2`
and then with the roles swapped using `|·|` symmetry) gives
`q·exp(−2ε) ≤ p ≤ q·exp(2ε)`; since both softmax entries lie in `[0,1]`, the
difference is squeezed into `[-(exp 2ε − 1), exp 2ε − 1]`.  Non-vacuous: at `ε = 0`
the bound is `0`, forcing `softmaxRow S = softmaxRow S2` exactly. -/
theorem softmaxRow_eps_of_eps (S S2 : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hbound : ∀ i j, |S i j - S2 i j| ≤ ε) (i j : Fin n) :
    |softmaxRow S i j - softmaxRow S2 i j| ≤ Real.exp (2 * ε) - 1 := by
  have hE : (1 : ℝ) ≤ Real.exp (2 * ε) := by
    rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
    exact Real.exp_le_exp.mpr (by linarith)
  have hple : softmaxRow S i j ≤ softmaxRow S2 i j * Real.exp (2 * ε) :=
    softmaxRow_le_softmaxRow_mul S S2 ε hbound i j
  have hother : softmaxRow S2 i j ≤ softmaxRow S i j * Real.exp (2 * ε) :=
    softmaxRow_le_softmaxRow_mul S2 S ε (fun a b => by rw [abs_sub_comm]; exact hbound a b) i j
  have hp1 : softmaxRow S i j ≤ 1 := softmaxRow_le_one S i j
  have hq1 : softmaxRow S2 i j ≤ 1 := softmaxRow_le_one S2 i j
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · nlinarith [hother, mul_nonneg (sub_nonneg.mpr hp1) (sub_nonneg.mpr hE)]
  · nlinarith [hple, mul_nonneg (sub_nonneg.mpr hq1) (sub_nonneg.mpr hE)]

/-! ## 4. ε-block logits give `(exp 2ε − 1)`-block attention -/

/-- **ε-block logits ⇒ `(exp 2ε − 1)`-block attention (PROVEN).**  This is the
result a real probe licenses.  A probe never sees an exactly-block logit matrix;
it sees one within `ε` of a block matrix `T (cell i) (cell j)`.  Composing the
block-preservation (§2) of the *exact* comparison `S2 i j := T (cell i) (cell j)`
with the Lipschitz estimate (§3) yields a block attention template `T2` that the
true softmax attention tracks within `exp(2ε) − 1` entrywise:

  `∃ T2, |softmaxRow S i j − T2 (cell i) (cell j)| ≤ exp(2ε) − 1`.

The template `T2` is the *exact* softmax of the block logits, so it is genuinely
cell-structured (load-bearing on both sides); the bound degrades gracefully to `0`
as `ε → 0`. -/
theorem softmaxRow_eps_block (S : Matrix (Fin n) (Fin n) ℝ)
    {I : Type*} [Fintype I] [DecidableEq I]
    (cell : Fin n → I) (T : I → I → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hblock : ∀ i j, |S i j - T (cell i) (cell j)| ≤ ε) :
    ∃ T2 : I → I → ℝ,
      ∀ i j, |softmaxRow S i j - T2 (cell i) (cell j)| ≤ Real.exp (2 * ε) - 1 := by
  set S2 : Matrix (Fin n) (Fin n) ℝ := fun i j => T (cell i) (cell j) with hS2
  obtain ⟨T2, hT2⟩ := softmaxRow_block_of_block S2 cell T (fun _ _ => rfl)
  refine ⟨T2, fun i j => ?_⟩
  rw [← hT2 i j]
  exact softmaxRow_eps_of_eps S S2 ε hε (fun a b => hblock a b) i j

/-! ## 5. Packaging softmax as a row-stochastic attention matrix -/

/-- **`softmaxRow S` as a `MachineLearning.AttentionMatrix` (PROVEN).**  The
row-wise softmax of any logit matrix is a nonnegative, row-stochastic matrix, i.e.
exactly the data the equitable-partition / quantum-walk machinery downstream
consumes.  This is the bridge object: feed it `S` from the QK-transpose probe and
get the attention operator the library analyses. -/
noncomputable def softmaxAttention (S : Matrix (Fin n) (Fin n) ℝ) :
    MachineLearning.AttentionMatrix (Fin n) where
  score := softmaxRow S
  nonneg := fun i j => (softmaxRow_pos S i j).le
  rowStoch := fun i => softmaxRow_rowSum S i

@[simp] theorem softmaxAttention_score (S : Matrix (Fin n) (Fin n) ℝ) :
    (softmaxAttention S).score = softmaxRow S := rfl

end EpsSoftmax
end Graphplay
