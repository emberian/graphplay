/-
# Graphplay.Integrations.AliBiAttention

**ALiBi — Attention with Linear Biases** (Press–Smith–Lewis, *Train Short, Test
Long: Attention with Linear Biases Enables Input Length Extrapolation*,
arXiv:2108.12409, 2021) — formalized as a **translation-equitable, path-graph
distance Hamiltonian** in the Graphplay walk picture.

## The one-line thesis

ALiBi replaces learned positional embeddings by adding, to every attention
score, a bias that is **linear in the token distance**:

  `score'[i][j] = score[i][j] − m · |i − j|`   (bidirectional / symmetric form)

The bias term `aliBiBias m n i j = −m·|i−j|` is a **Toeplitz** matrix (depends
only on `i − j`), hence **translation-equitable**: the cyclic shift is a graph
automorphism of the symmetrized score graph, exactly the structure
`StructuredAttention.circulantTranslationAut` packages.  In the quantum-walk
reading this bias *is* `−m · dist(i,j)` for the **path-graph metric** `|i−j|` on
the line `0—1—2—⋯—(n−1)` — the same positional path-walk the circuit-atlas finds
positional heads learning, and the **real sibling** of RoPE/PCT's complex
`U(1)`-phase (which lives in `NovelAttention` / the chiral files).

## ALiBi in the relative-position spectrum

| family            | bias / phase                | algebra                         | file              |
|-------------------|-----------------------------|---------------------------------|-------------------|
| **ALiBi**         | real `−m·\|i−j\|` (Toeplitz) | translation-equitable, path dist | **this file**     |
| **RoPE / PCT**    | complex `e^{iθ(i−j)}` phase  | translation-equitable, chiral    | NovelAttention/Chiral |
| sinusoidal (orig.)| additive `sin/cos` embed     | (not score-additive Toeplitz)    | —                 |

Both ALiBi and RoPE are **translation-equitable** (relative-position) schemes;
ALiBi is the *real Toeplitz* / path-distance member, RoPE the *complex
`U(1)`-phase* (chiral) member.  Cite Press–Smith–Lewis, arXiv:2108.12409
(ALiBi); Su et al., arXiv:2104.09864 (RoPE).

## Causal vs bidirectional

ALiBi as published is **causal** (decoder): for `j ≤ i` the bias is `−m·(i−j)`
and future keys `j > i` are masked.  The **bidirectional** (encoder) variant —
the one we take as primary, since it is the symmetric Hamiltonian the walk
machinery consumes — uses `−m·|i−j|`, symmetric in `i, j`.  The causal head is
the restriction of this symmetric bias to the lower triangle; see
`aliBiBias_causal_eq` for the `j ≤ i` agreement.

## What is proven axiom-clean (the deliverable)

* **Toeplitz / translation invariance.**  `aliBiBias_toeplitz` (depends only on
  `i − j`), `aliBiBias_symm` (symmetric), `aliBiBias_translation_invariant`
  (cyclic-shift invariance on `ZMod n`).  All elementary, **axiom-clean**.
* **Translation automorphism.**  `aliBiTranslationAut` — the shift `t ↦ t + k`
  is a `GraphAut` of the symmetrized ALiBi score graph (the pure-positional
  `S = 0` case), reusing the `StructuredAttention.circulantTranslationAut`
  pattern.  **Axiom-clean.**
* **Path-distance connection.**  `aliBiBias_eq_neg_pathDistance` — the bias is
  exactly `−m · pathDistance i j` for the line metric `|i−j|`.  **Axiom-clean.**
* **Length-extrapolation / scale-freeness.**  `aliBiBias_slope_length_independent`
  — the same slope `m` defines the bias at every `n`; the bias entry depends on
  `i, j` only through `|i−j|`, never on `n`.  This is the formal content of
  ALiBi's input-length extrapolation.  **Axiom-clean.**
* **Banded locality.**  `aliBiBandedCost` reuses `StructuredAttention.bandedCost`
  — a strong linear bias makes attention effectively local (`O(n·w)`).

## Honest `sorry`

* **None.**  Neither at the `def` level nor on the theorems: the structural facts
  are elementary, and the quantitative softmax-localization claim
  `aliBiBias_softmax_localizes` — that the out-of-band softmax mass decays
  *geometrically* in the band half-width `w` (`≤ K·rʷ`, `r = e^{−m} < 1`) — is now
  fully proven by the elementary `e^{−m·d}` tail bound, axiom-clean.

## References

* Press, Smith, Lewis, *Train Short, Test Long: Attention with Linear Biases
  Enables Input Length Extrapolation*, arXiv:2108.12409 (ICLR 2022).
* Su, Lu, Pan, Murtadha, Wen, Liu, *RoFormer: Enhanced Transformer with Rotary
  Position Embedding*, arXiv:2104.09864 (the complex `U(1)` sibling).
* Vaswani et al., *Attention Is All You Need*, NeurIPS 2017.
* `Graphplay.Integrations.StructuredAttention` (`circulantTranslationAut`,
  `circulantAttention_translation_invariant`, `bandedCost`),
  `Graphplay.Integrations.MachineLearning` (`AttentionMatrix`,
  `symmetrizedAttention`, `GraphAut`).
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Graphplay.Integrations.StructuredAttention

open scoped BigOperators

namespace Graphplay
namespace AliBiAttention

/-! ## 1. The ALiBi linear-distance bias -/

/-- **ALiBi bias matrix (bidirectional / symmetric form).**  For a slope
`m : ℝ` (per-head positive constant) and sequence length `n`, the ALiBi bias
added to the attention score between query token `i` and key token `j` is
`−m · |i − j|` — linear in the token distance.

This is the **encoder / bidirectional** variant, symmetric in `i, j`; it is the
real symmetric Toeplitz Hamiltonian the walk machinery consumes.  The published
**causal** (decoder) ALiBi bias is `−m·(i − j)` for `j ≤ i` (with `j > i`
masked); on the lower triangle `j ≤ i` the two agree (`aliBiBias_causal_eq`). -/
def aliBiBias (m : ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => -m * |(i : ℝ) - (j : ℝ)|

@[simp] theorem aliBiBias_apply (m : ℝ) (n : ℕ) (i j : Fin n) :
    aliBiBias m n i j = -m * |(i : ℝ) - (j : ℝ)| := rfl

/-- The diagonal of the ALiBi bias is `0`: a token has zero distance to itself,
so no positional penalty on self-attention. -/
@[simp] theorem aliBiBias_diag (m : ℝ) (n : ℕ) (i : Fin n) :
    aliBiBias m n i i = 0 := by
  simp [aliBiBias]

/-- **Causal agreement.**  On the lower triangle `j ≤ i` (the keys a causal
decoder may attend to), the bidirectional bias `−m·|i−j|` equals the published
causal bias `−m·(i−j)`, since `|i−j| = i−j` when `j ≤ i`.  This is the precise
sense in which the bidirectional form *restricts* to the causal ALiBi head. -/
theorem aliBiBias_causal_eq (m : ℝ) (n : ℕ) (i j : Fin n) (hji : (j : ℝ) ≤ (i : ℝ)) :
    aliBiBias m n i j = -m * ((i : ℝ) - (j : ℝ)) := by
  simp only [aliBiBias]
  rw [abs_of_nonneg (by linarith)]

/-! ## 2. Toeplitz / translation invariance — the relative-position structure

The defining algebraic fact about ALiBi: the bias depends **only on `i − j`**
(it is a Toeplitz matrix), and is **symmetric** in `i, j`.  This is the
translation-equitable structure — exactly the property that makes the cyclic
shift a graph automorphism (§3) and the additive characters the eigenvectors.
All proven axiom-clean (elementary `abs`-algebra). -/

/-- **Toeplitz property (PROVEN, axiom-clean).**  The ALiBi bias depends only on
the *signed* index difference `i − j`: if `(i:ℤ) − j = (i':ℤ) − j'` then the
two entries agree.  This is the matrix-Toeplitz statement (constant along
diagonals) and the translation-equitable signature of relative-position bias. -/
theorem aliBiBias_toeplitz (m : ℝ) (n : ℕ) (i j i' j' : Fin n)
    (h : (i : ℤ) - (j : ℤ) = (i' : ℤ) - (j' : ℤ)) :
    aliBiBias m n i j = aliBiBias m n i' j' := by
  simp only [aliBiBias]
  congr 2
  -- `|(i:ℝ) − j| = |(i':ℝ) − j'|` because the ℤ-differences agree, and the
  -- ℝ-difference is the ℤ-difference cast.
  have hcast : ((i : ℝ) - (j : ℝ)) = (((i : ℤ) - (j : ℤ) : ℤ) : ℝ) := by
    push_cast; ring
  have hcast' : ((i' : ℝ) - (j' : ℝ)) = (((i' : ℤ) - (j' : ℤ) : ℤ) : ℝ) := by
    push_cast; ring
  rw [hcast, hcast', h]

/-- **Symmetry (PROVEN, axiom-clean).**  The bidirectional ALiBi bias is
symmetric: `aliBiBias m n i j = aliBiBias m n j i`, because `|i−j| = |j−i|`.
This is what makes the symmetrized score graph real-symmetric (a genuine
Hermitian walk Hamiltonian). -/
theorem aliBiBias_symm (m : ℝ) (n : ℕ) (i j : Fin n) :
    aliBiBias m n i j = aliBiBias m n j i := by
  simp only [aliBiBias]
  rw [abs_sub_comm]

/-! ## 3. Translation-equitable structure on the cyclic token set

To package the ALiBi bias as the translation automorphism the equitable
machinery consumes, we move to the cyclic token set `ZMod n` (the periodic /
relative-position model, where the shift `t ↦ t + k` is a genuine permutation)
and read off the bias via a kernel `f : ZMod n → ℝ` that is symmetric.  The
pure-positional case is `S = 0`: the score graph is *exactly* the ALiBi bias,
and the shift is an automorphism.  We reuse the circulant machinery of
`StructuredAttention`. -/

/-- **The ALiBi bias as a circulant kernel on `ZMod n`.**  Picking a representative
`|·|` distance on the cycle via the `ZMod n` value, the cyclic ALiBi kernel is
`aliBiKernel m n d = −m · ‖d‖_cyc`, where `‖d‖_cyc = min (d.val) (n − d.val)` is
the cyclic distance to `0`.  On the *line* (non-wrapping) regime this restricts
to `−m·|i−j|`; here we use the cyclic distance so that translation invariance is
*exact* on `ZMod n` (the line bias is the `n → ∞` / non-wrapping reading).

We define it directly via the symmetric cyclic value, then feed it to
`StructuredAttention.circulantAttention`. -/
noncomputable def cyclicDist (n : ℕ) (d : ZMod n) : ℝ :=
  (min d.val (n - d.val) : ℕ)

/-- The cyclic ALiBi kernel `f(d) = −m · cyclicDist n d`. -/
noncomputable def aliBiKernel (m : ℝ) (n : ℕ) (d : ZMod n) : ℝ :=
  -m * cyclicDist n d

/-- **The cyclic distance is symmetric** (`cyclicDist n (−d) = cyclicDist n d`).
For `d = 0` both sides are `min 0 n = 0`; for `d ≠ 0`, `(−d).val = n − d.val`,
so the `min` of the pair is swapped, hence unchanged. -/
theorem cyclicDist_neg (n : ℕ) [NeZero n] (d : ZMod n) :
    cyclicDist n (-d) = cyclicDist n d := by
  unfold cyclicDist
  rcases eq_or_ne d 0 with hd | hd
  · subst hd; simp
  · haveI : NeZero d := ⟨hd⟩
    have hval : (-d).val = n - d.val := ZMod.val_neg_of_ne_zero d
    rw [hval]
    -- `min (n − v) (n − (n − v)) = min (n − v) v = min v (n − v)`.
    have hvlt : d.val < n := ZMod.val_lt d
    have : n - (n - d.val) = d.val := by omega
    rw [this, Nat.min_comm]

/-- The cyclic ALiBi kernel is symmetric: `f(−d) = f(d)`. -/
theorem aliBiKernel_symm (m : ℝ) (n : ℕ) [NeZero n] (d : ZMod n) :
    aliBiKernel m n (-d) = aliBiKernel m n d := by
  unfold aliBiKernel; rw [cyclicDist_neg]

/-- **Cyclic ALiBi attention** as a circulant score matrix on `ZMod n`: the pure
positional bias `A[i][j] = aliBiKernel m n (i − j) = −m·dist_cyc(i, j)`.  This is
`StructuredAttention.circulantAttention` with the ALiBi kernel — the `S = 0`
pure-positional ALiBi head. -/
noncomputable def cyclicAliBiAttention (m : ℝ) (n : ℕ) : Matrix (ZMod n) (ZMod n) ℝ :=
  StructuredAttention.circulantAttention n (aliBiKernel m n)

/-- **Translation invariance of cyclic ALiBi (PROVEN, axiom-clean).**  The cyclic
ALiBi score is invariant under simultaneous shift `A[i+k][j+k] = A[i][j]`:
directly `StructuredAttention.circulantAttention_translation_invariant` for the
ALiBi kernel.  This is the translation-equitable property — ALiBi's
relative-position structure made into the circulant/Toeplitz signature. -/
theorem cyclicAliBiAttention_translation_invariant (m : ℝ) (n : ℕ) (i j k : ZMod n) :
    cyclicAliBiAttention m n (i + k) (j + k) = cyclicAliBiAttention m n i j :=
  StructuredAttention.circulantAttention_translation_invariant n (aliBiKernel m n) i j k

/-- **The translation automorphism of the ALiBi score graph (PROVEN,
axiom-clean).**  For an `AttentionMatrix` over `ZMod n` whose score is the cyclic
ALiBi bias (`hbias : A.score i j = aliBiKernel m n (i − j)`), the shift
`t ↦ t + k` is a genuine `GraphAut` of the symmetrized token graph: the
linear-distance bias is translation-equitable, so the shift preserves the
symmetrized attention weights.

This packages the ALiBi positional structure as the automorphism the equitable
machinery consumes — the structural certificate that the translation-equitable
(orbit) reduction is valid for ALiBi.  Directly
`StructuredAttention.circulantTranslationAut`. -/
noncomputable def aliBiTranslationAut (m : ℝ) (n : ℕ) [NeZero n]
    (A : MachineLearning.AttentionMatrix (ZMod n))
    (hbias : ∀ i j, A.score i j = aliBiKernel m n (i - j)) (k : ZMod n) :
    MachineLearning.GraphAut A.symmetrizedAttention :=
  StructuredAttention.circulantTranslationAut n A (aliBiKernel m n) hbias k

/-! ## 4. The path-Hamiltonian connection

In the walk picture the ALiBi bias *is* `−m · dist(i,j)` for the **path-graph
metric** on the line `0—1—2—⋯—(n−1)`, where `dist(i,j) = |i−j|`.  This is the
precise statement connecting ALiBi to the positional path-walk: ALiBi penalizes
attention by the *graph distance along the path*. -/

/-- The **path-graph distance** on the line `Fin n` (vertices `0—1—⋯—(n−1)`):
`pathDistance i j = |i − j|`, the number of edges on the unique path between `i`
and `j`.  As a real number for the bias arithmetic. -/
def pathDistance (n : ℕ) (i j : Fin n) : ℝ := |(i : ℝ) - (j : ℝ)|

@[simp] theorem pathDistance_self (n : ℕ) (i : Fin n) : pathDistance n i i = 0 := by
  simp [pathDistance]

theorem pathDistance_symm (n : ℕ) (i j : Fin n) :
    pathDistance n i j = pathDistance n j i := by
  unfold pathDistance; rw [abs_sub_comm]

theorem pathDistance_nonneg (n : ℕ) (i j : Fin n) : 0 ≤ pathDistance n i j :=
  abs_nonneg _

/-- **ALiBi IS a path-distance bias (PROVEN, axiom-clean).**  The ALiBi bias is
*exactly* `−m · pathDistance i j` for the path-graph (line) metric `|i−j|`:

  `aliBiBias m n i j = −m · pathDistance n i j`.

This is the formal statement that "ALiBi = `−m·dist` on the path graph,"
connecting the linear positional bias to the quantum-walk on the line — the
positional path-walk the circuit-atlas finds positional heads learning. -/
theorem aliBiBias_eq_neg_pathDistance (m : ℝ) (n : ℕ) (i j : Fin n) :
    aliBiBias m n i j = -m * pathDistance n i j := rfl

/-- **The path-distance bias is monotone in distance (PROVEN, axiom-clean).**
For positive slope `m`, the ALiBi bias is *more negative* (penalizes more) the
farther apart the tokens are: if `pathDistance i j ≤ pathDistance i' j'` then
`aliBiBias m n i' j' ≤ aliBiBias m n i j`.  This is the qualitative
"attend less to distant tokens" content, made exact. -/
theorem aliBiBias_antitone_dist (m : ℝ) (n : ℕ) (hm : 0 ≤ m) (i j i' j' : Fin n)
    (hd : pathDistance n i j ≤ pathDistance n i' j') :
    aliBiBias m n i' j' ≤ aliBiBias m n i j := by
  rw [aliBiBias_eq_neg_pathDistance, aliBiBias_eq_neg_pathDistance]
  -- `−m·d' ≤ −m·d` ⟺ `m·d ≤ m·d'` (since `m ≥ 0`).
  have : m * pathDistance n i j ≤ m * pathDistance n i' j' :=
    mul_le_mul_of_nonneg_left hd hm
  linarith

/-! ## 5. Length-extrapolation / scale-freeness

The headline practical property of ALiBi — *train short, test long* — is, in
this framework, the **scale-freeness** of the translation-equitable structure:
the **same slope `m`** defines the bias at *every* sequence length `n`, because
the bias function `d ↦ −m·d` depends on `i, j` only through the relative
distance `|i−j|`, **never on `n`**.  There is no per-length learned table to
extrapolate; the relative-position law is `n`-independent by construction.  We
prove the precise statement. -/

/-- **The slope-`m` bias law is length-independent (PROVEN, axiom-clean).**  The
ALiBi bias entry depends on `i, j` only through the distance `|i − j|`, via the
single `n`-independent function `biasOfDist m d = −m·d`: for any two lengths
`n, n'` and index pairs with the *same real distance*, the bias entries agree.

This is the formal content of ALiBi's length-extrapolation: the translation
structure is **scale-free** — one slope `m` works at all lengths because the
relative-position bias is the same function `d ↦ −m·d` regardless of `n`. -/
theorem aliBiBias_slope_length_independent (m : ℝ) (n n' : ℕ)
    (i j : Fin n) (i' j' : Fin n')
    (hdist : |(i : ℝ) - (j : ℝ)| = |(i' : ℝ) - (j' : ℝ)|) :
    aliBiBias m n i j = aliBiBias m n' i' j' := by
  simp only [aliBiBias, hdist]

/-- The `n`-independent ALiBi bias-of-distance law `d ↦ −m·d`.  The bias matrix
at any length is the composition of this single function with the path distance:
`aliBiBias m n i j = biasOfDist m (pathDistance n i j)`. -/
def biasOfDist (m d : ℝ) : ℝ := -m * d

/-- **The bias factors through the `n`-free `biasOfDist ∘ pathDistance` (PROVEN,
axiom-clean).**  At every length `n`, `aliBiBias m n` is `biasOfDist m` composed
with the path distance — the bias matrix carries *no* `n`-dependent data beyond
the index set itself; the law is the fixed function `biasOfDist m`.  This is the
cleanest "scale-free" statement: the entire family `{aliBiBias m n}_n` is
generated by one length-independent rule. -/
theorem aliBiBias_factors (m : ℝ) (n : ℕ) (i j : Fin n) :
    aliBiBias m n i j = biasOfDist m (pathDistance n i j) := rfl

/-! ## 6. Banded locality — strong slope ⇒ effectively local

A large slope `m` makes the bias `−m·|i−j|` strongly penalize distant tokens, so
the softmax-normalized attention concentrates near the diagonal: ALiBi attention
is *effectively local*.  At the level of the structured-cost model this is the
banded apply of `StructuredAttention` — each row effectively touches only the
near-diagonal band — giving the `O(n·w)` reduction.  We reuse the existing
banded-cost machinery. -/

/-- The **effective banded cost** of ALiBi attention with effective window `w`:
reuses `StructuredAttention.bandedCost`.  A strong slope `m` means the off-band
weights are negligible, so the effective apply is `n·(2w+1)·d` mul-adds —
linear in `n`.  (The *exact* truncation error is the deep softmax-localization
claim `aliBiBias_softmax_localizes` below.) -/
def aliBiBandedCost (n w d : ℕ) : ℕ := StructuredAttention.bandedCost n w d

/-- **ALiBi effective cost is `O(n·w)` (PROVEN, `ℕ`-arithmetic).**  Reusing the
banded-cost theorem: `aliBiBandedCost n w d = n·((2w+1)·d)`, linear in `n` for a
fixed effective window `w`.  This is the structural-locality consequence of the
linear bias, at the operation-count level. -/
theorem aliBiBandedCost_eq (n w d : ℕ) :
    aliBiBandedCost n w d = n * ((2 * w + 1) * d) :=
  StructuredAttention.circulant_banded_cost n w d

/-- **ALiBi banded beats dense for sub-sequence windows (PROVEN).**  When the
effective window `2w+1 ≤ n`, the banded ALiBi apply does no more mul-adds than
the dense `O(n²)` apply.  Directly `StructuredAttention.banded_le_full`. -/
theorem aliBiBandedCost_le_full (n w d : ℕ) (hw : 2 * w + 1 ≤ n) :
    aliBiBandedCost n w d ≤ AttentionComplexity.fullCost n d :=
  StructuredAttention.banded_le_full n w d hw

/-! ### The quantitative localization claim (PROVEN, geometric tail)

The genuine *quantitative* localization — that the ALiBi slope `m` makes the
softmax over biased scores concentrate its mass on near-diagonal keys, with the
out-of-band mass decaying **geometrically** in the band half-width `w` — is the
elementary tail bound on `e^{−m·d}`.  We state and *prove* it precisely below
(`aliBiBias_softmax_localizes`): the out-of-band weight is `≤ K·rʷ` with
`r = e^{−m} < 1`.  The structural content above (Toeplitz, translation
automorphism, path-distance, scale-free, banded count) and this tail estimate are
the fully-proven deliverable. -/

/-- **Softmax localization under ALiBi slope — geometric out-of-band decay
(PROVEN).**

The genuine localization claim: the *un-normalized softmax mass outside* a band of
half-width `w` decays **geometrically in `w`**.  For a fixed positive slope `m`,
write `r := exp(−m) ∈ (0,1)`.  Then for every query `i` and every band half-width
`w`, the total ALiBi softmax weight on the out-of-band keys `{j : |i−j| > w}` is
bounded by `K · rʷ` with the explicit constant `K := n · exp(−m)`:
`∑_{|i−j| > w} exp(−m·|i−j|) ≤ K · rʷ`.

This is **genuinely non-vacuous** and *not* trivialised by `w := n − 1`: the bound
must hold for **all** `w` simultaneously, and `0 < r < 1`, so the right-hand side
`K·rʷ → 0` geometrically as `w` grows.  (The old `∃ m w, in-band ≥ (1−ε)·total`
shape was satisfied by `w := n−1`, where the band is the whole sequence; here the
content is the *decay rate* of the tail, which a degenerate `w` cannot fake — the
claim quantifies over every `w`.)  Because the normaliser `Zᵢ = ∑_k exp(−m|i−k|)
≥ exp(0) = 1` (the diagonal `k = i` term), the *normalised* out-of-band probability
is also `≤ K·rʷ`, so the band truncation of `aliBiBandedCost` incurs error that
vanishes geometrically — the precise content making the banded apply honest.

Proven by the elementary tail bound: each out-of-band term has `|i−j| ≥ w+1`, so
`exp(−m|i−j|) ≤ exp(−m(w+1)) = exp(−m)·rʷ`, and there are at most `n` such keys. -/
theorem aliBiBias_softmax_localizes (n : ℕ) (m : ℝ) (hm : 0 < m) :
    ∀ (w : ℕ) (i : Fin n),
      (∑ j ∈ Finset.univ.filter (fun j : Fin n => (w : ℝ) < |(i : ℝ) - (j : ℝ)|),
          Real.exp (aliBiBias m n i j))
        ≤ (n * Real.exp (-m)) * (Real.exp (-m)) ^ w := by
  intro w i
  set S := Finset.univ.filter (fun j : Fin n => (w : ℝ) < |(i : ℝ) - (j : ℝ)|) with hS
  -- Each out-of-band term is `≤ exp(-m)·rʷ`.
  have hterm : ∀ j ∈ S, Real.exp (aliBiBias m n i j)
      ≤ Real.exp (-m) * (Real.exp (-m)) ^ w := by
    intro j hj
    have hjmem : (w : ℝ) < |(i : ℝ) - (j : ℝ)| := by
      have := (Finset.mem_filter.mp (hS ▸ hj)).2
      simpa using this
    -- `exp(-m)·rʷ = exp(-m(w+1))`, and `|i-j| ≥ w+1 > w`, so `-m|i-j| ≤ -m(w+1)`.
    rw [aliBiBias_apply, ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hdist : (w : ℝ) + 1 ≤ |(i : ℝ) - (j : ℝ)| := by
      -- `|i - j|` is an integer distance `> w`, hence `≥ w + 1`.
      have hint : ∃ k : ℕ, |(i : ℝ) - (j : ℝ)| = (k : ℝ) := by
        refine ⟨(max i.val j.val) - (min i.val j.val), ?_⟩
        rcases le_total (i.val) (j.val) with h | h
        · rw [abs_of_nonpos (by
              have : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast h
              linarith)]
          rw [max_eq_right h, min_eq_left h]
          push_cast [Nat.cast_sub h]; ring
        · rw [abs_of_nonneg (by
              have : (j : ℝ) ≤ (i : ℝ) := by exact_mod_cast h
              linarith)]
          rw [max_eq_left h, min_eq_right h]
          push_cast [Nat.cast_sub h]; ring
      obtain ⟨k, hk⟩ := hint
      rw [hk] at hjmem ⊢
      have : w < k := by exact_mod_cast hjmem
      have : w + 1 ≤ k := this
      exact_mod_cast this
    have hkey : -m * |(i : ℝ) - (j : ℝ)| ≤ -m * ((w : ℝ) + 1) := by
      apply mul_le_mul_of_nonpos_left hdist (by linarith)
    nlinarith [hkey]
  -- Sum-of-bounded-terms `≤ card · bound ≤ n · bound`.
  calc (∑ j ∈ S, Real.exp (aliBiBias m n i j))
      ≤ ∑ _j ∈ S, Real.exp (-m) * (Real.exp (-m)) ^ w :=
        Finset.sum_le_sum hterm
    _ = S.card * (Real.exp (-m) * (Real.exp (-m)) ^ w) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ n * (Real.exp (-m) * (Real.exp (-m)) ^ w) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have : S.card ≤ Fintype.card (Fin n) := by
          simpa using Finset.card_le_univ S
        rw [Fintype.card_fin] at this
        exact_mod_cast this
    _ = (n * Real.exp (-m)) * (Real.exp (-m)) ^ w := by ring

/-! ## 7. Summary — ALiBi as translation-equitable path-distance bias

The ALiBi linear bias `−m·|i−j|` is, axiom-clean:

* **Toeplitz / translation-equitable** — depends only on `i − j`
  (`aliBiBias_toeplitz`), symmetric (`aliBiBias_symm`), cyclic-shift-invariant
  on `ZMod n` (`cyclicAliBiAttention_translation_invariant`), with the shift a
  genuine graph automorphism (`aliBiTranslationAut`).
* **A path-graph distance Hamiltonian** — `aliBiBias = −m · pathDistance`
  (`aliBiBias_eq_neg_pathDistance`), the positional path-walk on the line,
  monotone in distance (`aliBiBias_antitone_dist`).
* **Scale-free / length-extrapolating** — the same slope `m` at every `n`
  (`aliBiBias_slope_length_independent`); the family factors through the single
  `n`-free law `biasOfDist m` (`aliBiBias_factors`).
* **Effectively local** — the strong-slope banded apply is `O(n·w)`
  (`aliBiBandedCost_eq`, `aliBiBandedCost_le_full`).

The only honest gap is the deep quantitative softmax-localization
(`aliBiBias_softmax_localizes`).  ALiBi is the **real Toeplitz / path-distance**
member of the relative-position family; RoPE/PCT is the **complex `U(1)`-phase**
(chiral) sibling — both translation-equitable.  Cite Press–Smith–Lewis,
arXiv:2108.12409.
-/

end AliBiAttention
end Graphplay
