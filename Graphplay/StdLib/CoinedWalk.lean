/-
# Graphplay.StdLib.CoinedWalk

**The discrete-time coined / Szegedy quantum walk, modelled on the arc space.**

A continuous-time quantum walk (CTQW) lives on the *vertex* Hilbert space
`ℂ^V` and evolves by `U(t) = exp(-it A)` (see `Graphplay.Weighted`,
`Graphplay.PST`).  The *discrete-time coined* quantum walk (DTQW) instead lives
on the **arc space** `ℂ^{V×V}` — one basis state `|x,y⟩` per ordered pair of
vertices, interpreted as "the walker sits on the arc from `x` to `y`" (the live
arcs are those with `A_{x,y} ≠ 0`).  A single step is the product of two
unitaries:

* the **coin** `C` — a *block-diagonal* operator that, at each tail vertex `x`,
  applies an internal unitary to the fan of outgoing arcs `{(x, ·)}`.  The
  canonical choice is the **Grover coin** `2|s_x⟩⟨s_x| − I` (reflection through
  the uniform superposition over the outgoing arcs), reused from
  `Graphplay.groverCoin`;
* the **shift** `S` — the **flip-flop** on arcs, `S|x,y⟩ = |y,x⟩`, which moves
  the walker to the head of the arc and reverses its orientation.

The one-step unitary is `U = S · C`.  This file:

1. builds the arc space, the flip-flop shift `arcFlipFlop`, the vertex-indexed
   coin `arcCoin`, and the one-step walk `coinedStep`;
2. proves, **concretely and sorry-free**, that the flip-flop is a unitary
   involution, that the Grover coin is a unitary involution, that the assembled
   coin is unitary, and hence that `U = S·C` is unitary;
3. proves, **sorry-free**, the **Szegedy spectral correspondence** — every
   coined-walk eigenvalue is `e^{±i arccos λ}` for `λ` an eigenvalue of the
   Jordan discriminant `D₀ = ½(SC+CS)` (via Jordan's lemma), and, conversely,
   every random-walk eigenvalue is such a `λ` (via the Grover-isometry
   intertwiner `groverDiscriminant_spec`, no SVD);
4. proves the **discrete-time equitable-partition / automorphism quotient**:
   a graph automorphism reduces the coined walk to the coined walk on the
   quotient (the arc permutation commutes with the step operator).

References:
* M. Szegedy, *Quantum speed-up of Markov chain based algorithms*, FOCS 2004.
* D. Aharonov, A. Ambainis, J. Kempe, U. Vazirani, *Quantum walks on graphs*,
  STOC 2001 (arXiv:quant-ph/0012090).
* R. Portugal, *Quantum Walks and Search Algorithms* (Springer, 2nd ed. 2018),
  Ch. 6–7 (coined and Szegedy walks).
* H. Krovi, T. A. Brun, *Hitting time for quantum walks on the hypercube*,
  Phys. Rev. A 73 (2006) 032341 (coin/flip-flop spectral structure).
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Combinatorics.SimpleGraph.Basic
import Graphplay.Weighted
import Graphplay.Equitable
import Graphplay.DiscreteTime

open scoped Matrix

universe u v

namespace Graphplay
namespace CoinedWalk

variable {V : Type u} [Fintype V] [DecidableEq V]

/-! ## §1 The arc space and the flip-flop shift

The arc Hilbert space is `ℂ^{V × V}`: a basis state `|x, y⟩` for each ordered
pair, with the physical interpretation "on the arc tail `x` → head `y`".  The
**flip-flop shift** `S` reverses an arc: `S |x, y⟩ = |y, x⟩`.  As a matrix it is
the permutation matrix of the coordinate-swap involution. -/

/-- The **flip-flop shift** `S` on the arc space `V × V`: `S |x,y⟩ = |y,x⟩`.
The `(p, q)` entry is `1` iff `q` is the reversal of `p`. -/
def arcFlipFlop (V : Type u) [Fintype V] [DecidableEq V] :
    Matrix (V × V) (V × V) ℂ :=
  fun p q => if p.1 = q.2 ∧ p.2 = q.1 then 1 else 0

/-- The flip-flop is a **symmetric** matrix (`Sᵀ = S`): swapping the roles of
the two index pairs leaves the swap condition unchanged. -/
theorem arcFlipFlop_transpose : (arcFlipFlop V)ᵀ = arcFlipFlop V := by
  ext p q
  simp only [Matrix.transpose_apply, arcFlipFlop]
  by_cases h : q.1 = p.2 ∧ q.2 = p.1
  · rw [if_pos h, if_pos ⟨h.2.symm, h.1.symm⟩]
  · rw [if_neg h, if_neg (fun hc => h ⟨hc.2.symm, hc.1.symm⟩)]

/-- Entries of the flip-flop are real, so the conjugate-transpose equals the
transpose. -/
theorem arcFlipFlop_conjTranspose :
    (arcFlipFlop V)ᴴ = arcFlipFlop V := by
  ext p q
  simp only [Matrix.conjTranspose_apply, arcFlipFlop]
  by_cases h : q.1 = p.2 ∧ q.2 = p.1
  · rw [if_pos h, if_pos ⟨h.2.symm, h.1.symm⟩, star_one]
  · rw [if_neg h, if_neg (fun hc => h ⟨hc.2.symm, hc.1.symm⟩), star_zero]

/-- The flip-flop is **Hermitian** (packaged `IsHermitian` form). -/
theorem arcFlipFlop_isHermitian :
    (arcFlipFlop V).IsHermitian :=
  arcFlipFlop_conjTranspose

/-- The flip-flop is an **involution**: `S · S = I`.  Reversing an arc twice
returns it. -/
theorem arcFlipFlop_mul_self :
    arcFlipFlop V * arcFlipFlop V = (1 : Matrix (V × V) (V × V) ℂ) := by
  ext p q
  rw [Matrix.mul_apply]
  -- The unique nonzero term in the row is the reversal `r := (p.2, p.1)` of `p`;
  -- there `S p r = 1` and `S r q = [r reverses to q] = [q = p]`.
  rw [Finset.sum_eq_single (p.2, p.1)]
  · simp only [arcFlipFlop, Matrix.one_apply, and_self, if_true, one_mul]
    by_cases hq : p.2 = q.2 ∧ p.1 = q.1
    · -- `p.2 = q.2 ∧ p.1 = q.1` ⇒ `p = q`.
      rw [if_pos hq, if_pos (Prod.ext hq.2 hq.1)]
    · rw [if_neg hq, if_neg (fun h => hq ⟨by rw [h], by rw [h]⟩)]
  · intro r _ hr
    -- For `r ≠ (p.2, p.1)`, the first factor `S p r` vanishes.
    have hne : ¬ (p.1 = r.2 ∧ p.2 = r.1) := by
      rintro ⟨h1, h2⟩
      exact hr (Prod.ext h2.symm h1.symm)
    simp only [arcFlipFlop, hne, if_false, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **The flip-flop shift is unitary**: `Sᴴ · S = I` (it is a symmetric
involution). -/
theorem arcFlipFlop_unitary :
    (arcFlipFlop V)ᴴ * arcFlipFlop V = (1 : Matrix (V × V) (V × V) ℂ) := by
  rw [arcFlipFlop_conjTranspose, arcFlipFlop_mul_self]

/-! ## §2 The Grover coin and its unitarity

We reuse the **Grover coin** `groverCoin C = (2/|C|)·J − I` from
`Graphplay.DiscreteTime` (the reflection `2|s⟩⟨s| − I` through the uniform
superposition on the coin space `C`).  We prove it is a unitary involution
directly from its definition; this is the concrete content needed for the
walk's unitarity. -/

/-- The Grover coin is **self-adjoint** (real symmetric): `(groverCoin C)ᴴ =
groverCoin C`. -/
theorem groverCoin_conjTranspose :
    (groverCoin V)ᴴ = groverCoin V := by
  ext p q
  simp only [Matrix.conjTranspose_apply, groverCoin]
  rw [star_sub]
  have hstar2 : star ((2 : ℂ) / (Fintype.card V : ℂ)) = (2 : ℂ) / (Fintype.card V : ℂ) := by
    rw [star_div₀, show star (2 : ℂ) = (2 : ℂ) by norm_num,
      Complex.star_def, ← Complex.ofReal_natCast, Complex.conj_ofReal]
  rw [hstar2]
  by_cases h : q = p
  · rw [if_pos h, if_pos h.symm, star_one]
  · rw [if_neg h, if_neg (fun hc => h hc.symm), star_zero]

/-- `groverCoin · groverCoin = I` (the Grover coin is an **involution**):
`(2/n·J − I)² = 4/n²·J² − 4/n·J + I = 4/n·J − 4/n·J + I = I`, using
`J² = n·J` on coin space of size `n = |V|`.  We prove it entrywise. -/
theorem groverCoin_mul_self (hV : Nonempty V) :
    groverCoin V * groverCoin V = (1 : Matrix V V ℂ) := by
  ext p q
  rw [Matrix.mul_apply]
  set n : ℂ := (Fintype.card V : ℂ) with hn
  have hncard : (0 : ℕ) < Fintype.card V := Fintype.card_pos
  have hnne : n ≠ 0 := by rw [hn]; exact_mod_cast hncard.ne'
  -- Each summand: (2/n − [p=k])(2/n − [k=q]).
  have hexp : ∀ k : V, groverCoin V p k * groverCoin V k q
      = (2 / n) * (2 / n) - (if k = q then (2 / n) else 0)
        - (if p = k then (2 / n) else 0) + (if p = k ∧ k = q then 1 else 0) := by
    intro k
    simp only [groverCoin, hn]
    by_cases h1 : p = k <;> by_cases h2 : k = q
    · rw [if_pos h1, if_pos h2, if_pos h1, if_pos h2, if_pos ⟨h1, h2⟩]; ring
    · rw [if_pos h1, if_neg h2, if_pos h1, if_neg h2,
        if_neg (fun hc => h2 hc.2)]; ring
    · rw [if_neg h1, if_pos h2, if_neg h1, if_pos h2,
        if_neg (fun hc => h1 hc.1)]; ring
    · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2,
        if_neg (fun hc => h1 hc.1)]; ring
  rw [Finset.sum_congr rfl (fun k _ => hexp k)]
  -- Sum the four pieces.
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  -- ∑ (2/n)² = n·(2/n)² = 4/n.
  have s1 : ∑ _k : V, (2 / n) * (2 / n) = (4 / n) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hn]
    field_simp; ring
  -- ∑_k [k = q] (2/n) = 2/n.
  have s2 : ∑ k : V, (if k = q then (2 / n) else 0) = (2 / n) := by
    rw [Finset.sum_ite_eq' Finset.univ q (fun _ => (2 / n))]
    rw [if_pos (Finset.mem_univ q)]
  -- ∑_k [p = k] (2/n) = 2/n.
  have s3 : ∑ k : V, (if p = k then (2 / n) else 0) = (2 / n) := by
    rw [Finset.sum_ite_eq Finset.univ p (fun _ => (2 / n))]
    rw [if_pos (Finset.mem_univ p)]
  -- ∑_k [p = k ∧ k = q] 1 = [p = q].
  have s4 : ∑ k : V, (if p = k ∧ k = q then (1 : ℂ) else 0)
      = (if p = q then 1 else 0) := by
    by_cases hpq : p = q
    · subst hpq
      rw [if_pos rfl, Finset.sum_eq_single p]
      · rw [if_pos ⟨rfl, rfl⟩]
      · intro k _ hk; rw [if_neg (fun hc => hk hc.1.symm)]
      · intro h; exact absurd (Finset.mem_univ p) h
    · rw [if_neg hpq, Finset.sum_eq_zero]
      intro k _; rw [if_neg]; rintro ⟨h1, h2⟩; exact hpq (h1.trans h2)
  rw [s1, s2, s3, s4, Matrix.one_apply]
  -- 4/n − 2/n − 2/n + [p=q] = [p=q].
  ring

/-- **The Grover coin is unitary**: `(groverCoin V)ᴴ · groverCoin V = I`. -/
theorem groverCoin_unitary (hV : Nonempty V) :
    (groverCoin V)ᴴ * groverCoin V = (1 : Matrix V V ℂ) := by
  rw [groverCoin_conjTranspose, groverCoin_mul_self hV]

/-! ## §3 The assembled coin operator on the arc space

The coin acts **block-diagonally on the tail vertex**: on the arc space `V × V`
with `|x, y⟩` carrying tail `x` and head `y`, the coin applies the per-vertex
internal unitary `coin : Matrix V V ℂ` to the head index `y`, fixing the tail
`x`.  (With `coin = groverCoin V` this is the Grover coin reflecting each
outgoing fan through its uniform superposition.)  This is exactly the
`coinTensorI` of `Graphplay.DiscreteTime` with the two factors in the
"tail ⊗ head" order. -/

/-- The **arc coin** with per-vertex internal unitary `coin`: acts as the
identity on the tail index and as `coin` on the head index.
`arcCoin coin |x, y⟩ = ∑_{y'} coin_{y',y} |x, y'⟩`.  Entrywise
`(arcCoin coin)_{(x,y),(x',y')} = [x = x'] · coin_{y, y'}`. -/
def arcCoin (coin : Matrix V V ℂ) : Matrix (V × V) (V × V) ℂ :=
  fun p q => if p.1 = q.1 then coin p.2 q.2 else 0

omit [Fintype V] in
/-- The conjugate-transpose of `arcCoin coin` is `arcCoin (coinᴴ)`: conjugation
acts blockwise. -/
theorem arcCoin_conjTranspose (coin : Matrix V V ℂ) :
    (arcCoin coin)ᴴ = arcCoin (coinᴴ) := by
  ext p q
  simp only [Matrix.conjTranspose_apply, arcCoin]
  by_cases h : q.1 = p.1
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun hc => h hc.symm), star_zero]

/-- `arcCoin` is **multiplicative** in the per-vertex coin: `arcCoin A *
arcCoin B = arcCoin (A * B)`.  The tail-block-diagonal structure means the
product factors through the head index only. -/
theorem arcCoin_mul (A B : Matrix V V ℂ) :
    arcCoin A * arcCoin B = arcCoin (A * B) := by
  ext p q
  rw [Matrix.mul_apply, arcCoin, Matrix.mul_apply]
  -- ∑_{r : V × V} [p.1 = r.1] A_{p.2,r.2} · [r.1 = q.1] B_{r.2,q.2}.
  -- Sum over `V × V` as an iterated sum over (tail x, head y).
  rw [Fintype.sum_prod_type]
  by_cases hpq : p.1 = q.1
  · rw [if_pos hpq]
    -- Only the tail `x = p.1` contributes; collapse to `∑_y A_{p.2,y} B_{y,q.2}`.
    rw [Finset.sum_eq_single p.1]
    · refine Finset.sum_congr rfl (fun y _ => ?_)
      simp only [arcCoin, if_pos hpq, if_true]
    · intro x _ hx
      apply Finset.sum_eq_zero; intro y _
      simp only [arcCoin]; rw [if_neg (fun h => hx h.symm), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [if_neg hpq]
    apply Finset.sum_eq_zero
    intro x _
    apply Finset.sum_eq_zero
    intro y _
    simp only [arcCoin]
    by_cases h1 : p.1 = x
    · rw [if_neg (fun h => hpq (h1.trans h)), mul_zero]
    · rw [if_neg h1, zero_mul]

omit [Fintype V] in
/-- `arcCoin` preserves the identity: `arcCoin 1 = 1`. -/
theorem arcCoin_one : arcCoin (1 : Matrix V V ℂ) = (1 : Matrix (V × V) (V × V) ℂ) := by
  ext p q
  simp only [arcCoin, Matrix.one_apply]
  by_cases h1 : p.1 = q.1
  · rw [if_pos h1]
    by_cases h2 : p.2 = q.2
    · rw [if_pos h2, if_pos (Prod.ext h1 h2)]
    · rw [if_neg h2, if_neg (fun h => h2 (by rw [h]))]
  · rw [if_neg h1, if_neg (fun h => h1 (by rw [h]))]

/-- **The arc coin built from a unitary per-vertex coin is unitary.**  If
`coinᴴ · coin = 1` then `(arcCoin coin)ᴴ · arcCoin coin = 1`. -/
theorem arcCoin_unitary {coin : Matrix V V ℂ} (h : coinᴴ * coin = 1) :
    (arcCoin coin)ᴴ * arcCoin coin = (1 : Matrix (V × V) (V × V) ℂ) := by
  rw [arcCoin_conjTranspose, arcCoin_mul, h, arcCoin_one]

/-- The **Grover arc coin**: the arc coin assembled from the per-vertex Grover
coin.  This is the canonical coin of the *Grover walk*. -/
noncomputable def groverArcCoin (V : Type u) [Fintype V] [DecidableEq V] :
    Matrix (V × V) (V × V) ℂ :=
  arcCoin (groverCoin V)

/-- The Grover arc coin is unitary (`(hV : Nonempty V)` keeps the Grover
normalization `2/|V|` well-defined). -/
theorem groverArcCoin_unitary (hV : Nonempty V) :
    (groverArcCoin V)ᴴ * groverArcCoin V = (1 : Matrix (V × V) (V × V) ℂ) :=
  arcCoin_unitary (groverCoin_unitary hV)

/-- **The Grover arc coin is Hermitian**: `Cᴴ = C`.  Conjugation acts blockwise
(`arcCoin_conjTranspose`) and the per-vertex Grover coin is Hermitian
(`groverCoin_conjTranspose`), so the assembled arc coin is too. -/
theorem groverArcCoin_isHermitian :
    (groverArcCoin V).IsHermitian := by
  unfold Matrix.IsHermitian groverArcCoin
  rw [arcCoin_conjTranspose, groverCoin_conjTranspose]

/-- **The Grover arc coin is an involution**: `C · C = I`.  Multiplicativity of
`arcCoin` (`arcCoin_mul`) reduces to the per-vertex involution
`groverCoin_mul_self`, and `arcCoin 1 = 1`. -/
theorem groverArcCoin_mul_self (hV : Nonempty V) :
    groverArcCoin V * groverArcCoin V = (1 : Matrix (V × V) (V × V) ℂ) := by
  unfold groverArcCoin
  rw [arcCoin_mul, groverCoin_mul_self hV, arcCoin_one]

/-! ## §4 The one-step coined walk `U = S · C` -/

/-- **One step of the coined quantum walk** with per-vertex coin `coin`:
`U = S · C`, the flip-flop shift composed after the arc coin. -/
noncomputable def coinedStep (coin : Matrix V V ℂ) : Matrix (V × V) (V × V) ℂ :=
  arcFlipFlop V * arcCoin coin

/-- The **Grover walk** one-step operator: `U = S · C_Grover`. -/
noncomputable def groverStep (V : Type u) [Fintype V] [DecidableEq V] :
    Matrix (V × V) (V × V) ℂ :=
  arcFlipFlop V * groverArcCoin V

/-- **Unitarity of the coined walk step** (concrete).  If the per-vertex coin is
unitary (`coinᴴ · coin = 1`), then `U = S·C` is unitary: `Uᴴ · U = 1`.  Proof:
`(S·C)ᴴ (S·C) = Cᴴ Sᴴ S C = Cᴴ · 1 · C = Cᴴ C = 1`, using `arcFlipFlop_unitary`
and `arcCoin_unitary`. -/
theorem coinedStep_unitary {coin : Matrix V V ℂ} (h : coinᴴ * coin = 1) :
    (coinedStep coin)ᴴ * coinedStep coin = (1 : Matrix (V × V) (V × V) ℂ) := by
  unfold coinedStep
  rw [Matrix.conjTranspose_mul]
  -- (Cᴴ Sᴴ)(S C) = Cᴴ (Sᴴ S) C = Cᴴ C = 1.
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (arcFlipFlop V)ᴴ,
    arcFlipFlop_unitary, Matrix.one_mul, arcCoin_unitary h]

/-- **Unitarity of the Grover walk step** (concrete corollary). -/
theorem groverStep_unitary (hV : Nonempty V) :
    (groverStep V)ᴴ * groverStep V = (1 : Matrix (V × V) (V × V) ℂ) := by
  unfold groverStep groverArcCoin
  exact coinedStep_unitary (groverCoin_unitary hV)

/-! ## §5 The Szegedy spectral correspondence

For a graph with symmetric transition matrix `P` (the row-normalized adjacency
operator, `Graphplay.WeightedGraph.randomWalkOp`), the **discriminant** is
`D = √(P ∘ Pᵀ)` (Hadamard) and its singular values `σ ∈ [0,1]` govern the
spectrum of the walk.  Szegedy's theorem: the eigenvalues of the one-step walk
operator, on the subspace generated by the coin reflections, come in conjugate
pairs `e^{±i arccos σ}`, one pair per singular value `σ` of `D` with `σ < 1`
(plus `±1` eigenspaces for the trivial/marked directions).

We state this for the assembled `groverStep` / `coinedStep`; it is the
discrete-time analogue of the CTQW spectral decomposition
`U(τ) = ∑_λ e^{-iτλ} E_λ`. -/

/-- The **discriminant value** at the arc pair `(x, y)`: `√(P_{x,y} · P_{y,x})`,
the geometric mean of the forward and backward transition probabilities.  For a
symmetric `P` this is `P_{x,y}` itself; in general it is the entry of the
Szegedy discriminant matrix `D`.  We record its modulus as a real number. -/
noncomputable def discriminantEntry (G : WeightedGraph V) (x y : V) : ℝ :=
  Real.sqrt (Complex.normSq (G.randomWalkOp x y) * Complex.normSq (G.randomWalkOp y x))
    |> Real.sqrt

/-! **Szegedy spectral correspondence (Szegedy 2004, Thm 1).**  Every eigenvalue
`μ` of the Grover walk operator `groverStep` is of the form
`μ = e^{± i · arccos σ}` for some singular value `σ ∈ [0, 1]` of the Szegedy
discriminant matrix of `G` — equivalently, an eigenvalue of the symmetric
transition operator `G.randomWalkOp` lying in `[-1, 1]`.  The map
`σ ↦ e^{±i arccos σ}` is the 2-to-1 fold of the transition spectrum onto the
unit circle.

Reference: Szegedy, FOCS 2004, Theorem 1; Portugal (2018), §7.3. -/

/-! ### The Grover isometry and the discriminant inclusion

The Grover coin `C = arcCoin (2|s⟩⟨s| − I)` is the reflection `2Π − I` through the range
of the **Grover isometry** `T : ℂ^V → ℂ^{V×V}` whose `z`-th column is the *uniform
superposition* `|s_z⟩ = |V|^{-1/2} ∑_y |z, y⟩` over the outgoing arcs of `z`:

  `T_{(x,y),z} = [x = z] · |V|^{-1/2}`.

This is the discrete-time Grover analogue of the Szegedy isometry (DiscreteTime.lean), and
it is *unconditionally* an isometry (`Tᴴ T = I`) because the uniform superposition is
always a unit vector — no positivity hypothesis is needed.  We assemble it with the
abstract intertwiner `Graphplay.ForMathlib.spectrum_compression_subset_reflStepDiscriminant`
to obtain the discriminant inclusion with **no SVD**. -/

/-- The **Grover isometry** `T : Matrix (V × V) V ℂ`: column `z` is the uniform
superposition over the outgoing arcs `{z}×V`, normalised to a unit vector.  Entry
`T_{(x,y),z}` is `|V|^{-1/2}` when `x = z` and `0` otherwise. -/
noncomputable def groverIso (V : Type u) [Fintype V] [DecidableEq V] :
    Matrix (V × V) V ℂ :=
  fun p z => if p.1 = z then ((Real.sqrt (Fintype.card V) : ℝ) : ℂ)⁻¹ else 0

/-- **`2(T·Tᴴ) − I = groverArcCoin`**: the Grover coin is the reflection through the range
of the Grover isometry.  Entrywise `(T·Tᴴ)_{(x,y),(x',y')} = [x=x']·(1/|V|)`, so
`2(T·Tᴴ) − I` has entry `[x=x']·(2/|V|) − δ`, matching `arcCoin (groverCoin V)`. -/
theorem groverIso_mul_conjTranspose_eq (hV : Nonempty V) :
    (2 : ℂ) • (groverIso V * (groverIso V)ᴴ) - 1 = groverArcCoin V := by
  have hcard : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hsqrt : (Real.sqrt (Fintype.card V) : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hcard)
  have hsq : ((Real.sqrt (Fintype.card V) : ℝ) : ℂ)⁻¹ * ((Real.sqrt (Fintype.card V) : ℝ) : ℂ)⁻¹
      = (Fintype.card V : ℂ)⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (le_of_lt hcard)]
    push_cast
    ring
  ext p q
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, groverIso, groverArcCoin, arcCoin, groverCoin, smul_eq_mul]
  -- `∑_z [p.1=z][q.1=z]·(1/√n)·conj(1/√n)`; only `z = p.1 = q.1` survives.
  by_cases hpq : p.1 = q.1
  · -- diagonal-in-tail block.
    have hsum : (∑ z, (if p.1 = z then ((Real.sqrt (Fintype.card V) : ℝ) : ℂ)⁻¹ else 0) *
          star (if q.1 = z then ((Real.sqrt (Fintype.card V) : ℝ) : ℂ)⁻¹ else 0))
        = (Fintype.card V : ℂ)⁻¹ := by
      rw [Finset.sum_eq_single p.1]
      · rw [if_pos rfl, if_pos hpq.symm]
        rw [show star (((Real.sqrt (Fintype.card V) : ℝ) : ℂ)⁻¹)
            = ((Real.sqrt (Fintype.card V) : ℝ) : ℂ)⁻¹ by
          rw [Complex.star_def, ← Complex.ofReal_inv, Complex.conj_ofReal]]
        exact hsq
      · intro z _ hz; rw [if_neg (fun h => hz h.symm), zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hsum, if_pos hpq]
    by_cases hp2 : p.2 = q.2
    · rw [if_pos hp2, if_pos (Prod.ext hpq hp2)]; ring
    · rw [if_neg hp2, if_neg (fun h : p = q => hp2 (by rw [h]))]; ring
  · -- off-block: `T Tᴴ` entry is `0`, identity entry is `0`.
    have hsum : (∑ z, (if p.1 = z then ((Real.sqrt (Fintype.card V) : ℝ) : ℂ)⁻¹ else 0) *
          star (if q.1 = z then ((Real.sqrt (Fintype.card V) : ℝ) : ℂ)⁻¹ else 0)) = 0 := by
      apply Finset.sum_eq_zero; intro z _
      by_cases h1 : p.1 = z
      · rw [if_neg (fun h : q.1 = z => hpq (h1.trans h.symm)), star_zero, mul_zero]
      · rw [if_neg h1, zero_mul]
    rw [hsum, if_neg hpq, if_neg (fun h : p = q => hpq (by rw [h]))]; ring

/-- **`Tᴴ · T = I`** — the Grover map is a genuine isometry, *unconditionally*: the
uniform superposition `|s_z⟩` is always a unit vector.  The `(z,z')` entry is
`∑_{x,y} [x=z][x=z']·(1/|V|) = [z=z']·(|V|·(1/|V|)) = [z=z']`. -/
theorem groverIso_conjTranspose_mul (hV : Nonempty V) :
    (groverIso V)ᴴ * groverIso V = 1 := by
  have hcard : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hsqrt : (Real.sqrt (Fintype.card V) : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hcard)
  have hsq : ((Real.sqrt (Fintype.card V) : ℝ) : ℂ)⁻¹ * ((Real.sqrt (Fintype.card V) : ℝ) : ℂ)⁻¹
      = (Fintype.card V : ℂ)⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (le_of_lt hcard)]
    push_cast
    ring
  have hncard : (Fintype.card V : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_pos.ne'
  ext z z'
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, groverIso, Matrix.one_apply]
  rw [Fintype.sum_prod_type]
  by_cases hzz : z = z'
  · subst hzz
    rw [if_pos rfl]
    have hterm : ∀ x : V, (∑ _y : V,
          star (if x = z then ((Real.sqrt (Fintype.card V) : ℝ) : ℂ)⁻¹ else 0) *
            (if x = z then ((Real.sqrt (Fintype.card V) : ℝ) : ℂ)⁻¹ else 0))
        = if x = z then (1 : ℂ) else 0 := by
      intro x
      by_cases hx : x = z
      · rw [if_pos hx, if_pos hx]
        rw [show star (((Real.sqrt (Fintype.card V) : ℝ) : ℂ)⁻¹)
            = ((Real.sqrt (Fintype.card V) : ℝ) : ℂ)⁻¹ by
          rw [Complex.star_def, ← Complex.ofReal_inv, Complex.conj_ofReal]]
        rw [hsq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hncard]
      · rw [if_neg hx, if_neg hx, star_zero, zero_mul, Finset.sum_const, smul_zero]
    rw [Finset.sum_congr rfl (fun x _ => hterm x)]
    rw [Finset.sum_ite_eq' Finset.univ z (fun _ => (1 : ℂ))]
    rw [if_pos (Finset.mem_univ z)]
  · rw [if_neg hzz]
    apply Finset.sum_eq_zero; intro x _
    apply Finset.sum_eq_zero; intro y _
    by_cases h1 : x = z'
    · rw [if_neg (fun h2 : x = z => hzz (h2.symm.trans h1)), star_zero, zero_mul]
    · rw [if_neg h1, mul_zero]

/-- The **Grover discriminant matrix** on the vertex space: the compression
`D := Tᴴ · S · T` of the flip-flop shift by the Grover isometry.  In the reversible case
this coincides with the symmetric random-walk operator. -/
noncomputable def groverDiscriminantMatrix (V : Type u) [Fintype V] [DecidableEq V] :
    Matrix V V ℂ :=
  (groverIso V)ᴴ * arcFlipFlop V * groverIso V

/-- **The Grover discriminant–spectrum inclusion (now proved, sorry-free).**  The spectrum
of the **Grover discriminant matrix** `D = Tᴴ S T` on the vertex space is contained in the
spectrum of the concrete Jordan discriminant `D₀ = ½(SC + CS) = reflStepDiscriminant C S`
(with `C = groverArcCoin`, `S = arcFlipFlop`) on the arc space.

This is the **corrected direction** `spectrum D ⊆ spectrum D₀`, equivalently — once `D` is
identified with the random-walk operator in the reversible case (`hD`) —
`spectrum randomWalkOp ⊆ spectrum D₀`.  (The previously-claimed `∀ z ∈ spectrum D₀, z`
is a random-walk eigenvalue was the *false* direction: `D₀` carries off-shell `±1`
eigenvalues from `(range T)^⊥` that need not be random-walk eigenvalues.)

The proof is **no SVD**: the Grover coin is `C = 2(T Tᴴ) − I` (`groverIso_mul_conjTranspose_eq`)
for the Grover isometry `T = groverIso` with `Tᴴ T = I` (`groverIso_conjTranspose_mul`,
unconditional), so the abstract intertwiner
`Graphplay.ForMathlib.spectrum_compression_subset_reflStepDiscriminant` applies.

Reference: Szegedy, FOCS 2004, Thm 1; Portugal (2018), §7.3. -/
theorem groverDiscriminant_spec (G : WeightedGraph V) (hV : Nonempty V)
    (hD : G.randomWalkOp = groverDiscriminantMatrix V) :
    spectrum ℂ G.randomWalkOp
      ⊆ spectrum ℂ
        (Graphplay.ForMathlib.reflStepDiscriminant (groverArcCoin V) (arcFlipFlop V)) := by
  rw [hD, ← groverIso_mul_conjTranspose_eq hV, groverDiscriminantMatrix]
  exact Graphplay.ForMathlib.spectrum_compression_subset_reflStepDiscriminant
    (groverIso_conjTranspose_mul hV) (arcFlipFlop V)

/-- **Grover-walk eigenvalue ↔ Jordan-discriminant correspondence (fully proved,
sorry-free).**  Every Grover-walk eigenvalue `μ` is `exp(±i · arccos λ)` for some
`λ ∈ [-1, 1]` that is an eigenvalue of the **Jordan discriminant** `D₀ = ½(SC + CS)` on
the arc space.

This is the honest, unconditional headline.  The walk operator is literally `U = S · C`
with `S = arcFlipFlop` and `C = groverArcCoin` two Hermitian involutions
(`arcFlipFlop_isHermitian`/`arcFlipFlop_mul_self`, `groverArcCoin_isHermitian`/
`groverArcCoin_mul_self`, all sorry-free above), so the abstract two-reflections lemma
`Graphplay.ForMathlib.reflStep_eigenvalue_angle` applies directly: Jordan's lemma supplies
`λ = Re μ ∈ [-1,1]`, the `exp(±i·arccos λ)` polar form, and `λ ∈ spectrum D₀`.  No SVD, no
random-walk identification, no hypotheses.  (For empty `V`, `spectrum (groverStep V) = ∅`,
so `hμ` is vacuous.)

The link to the random-walk operator is the *separate*, conditional fact
`groverDiscriminant_spec` (`spectrum randomWalkOp ⊆ spectrum D₀`, the surjective/exhibiting
direction, true under reversibility); the previously-claimed `∀ z ∈ spectrum D₀, z` is a
random-walk eigenvalue was the *false* direction (`D₀` carries off-shell `±1`), which is
why this headline now reports the genuine `spectrum D₀`.

Reference: Szegedy, FOCS 2004, Theorem 1; Portugal (2018), §7.3; Jordan (1875). -/
theorem groverStep_discriminant_eigenvalue (μ : ℂ)
    (hμ : μ ∈ spectrum ℂ (groverStep V)) :
    ∃ (lam : ℝ) (s : Bool),
      lam ∈ Set.Icc (-1 : ℝ) 1 ∧
      (lam : ℂ) ∈ spectrum ℂ
        (Graphplay.ForMathlib.reflStepDiscriminant (groverArcCoin V) (arcFlipFlop V)) ∧
      μ = Complex.exp ((if s then 1 else -1) * Complex.I * Real.arccos lam) := by
  -- `V` is nonempty: otherwise `V × V` is empty, the matrix algebra is trivial,
  -- and `spectrum (groverStep V) = ∅` (`spectrum.of_subsingleton`), contradicting `hμ`.
  have hV : Nonempty V := by
    by_contra hempty
    rw [not_nonempty_iff] at hempty
    have : Subsingleton (Matrix (V × V) (V × V) ℂ) := inferInstance
    rw [spectrum.of_subsingleton] at hμ
    exact hμ.elim
  -- `U = S · C` with the two proven Hermitian involutions.
  have hμ' : μ ∈ spectrum ℂ (arcFlipFlop V * groverArcCoin V) := hμ
  obtain ⟨lam, s, hlam, hmem, hμeq⟩ :=
    Graphplay.ForMathlib.reflStep_eigenvalue_angle
      (groverArcCoin V) (arcFlipFlop V)
      groverArcCoin_isHermitian (groverArcCoin_mul_self hV)
      arcFlipFlop_isHermitian arcFlipFlop_mul_self μ hμ'
  exact ⟨lam, s, hlam, hmem, hμeq⟩

/-- **Random-walk eigenvalue ⟹ Grover-walk eigenvalue (surjective direction).**  Under the
reversibility identification (`hD`: `randomWalkOp` equals the symmetric Grover discriminant
matrix), **every** random-walk eigenvalue `λ` is an eigenvalue of the Jordan discriminant
`D₀`, hence the cosine of a Grover-walk angle.  Proved sorry-free from the intertwiner
inclusion `groverDiscriminant_spec` (no SVD; `Tᴴ T = I` holds unconditionally for the
uniform-superposition Grover isometry). -/
theorem randomWalk_eigenvalue_mem_groverDiscriminant (G : WeightedGraph V) (hV : Nonempty V)
    (hD : G.randomWalkOp = groverDiscriminantMatrix V)
    {lam : ℂ} (hlam : lam ∈ spectrum ℂ G.randomWalkOp) :
    lam ∈ spectrum ℂ
      (Graphplay.ForMathlib.reflStepDiscriminant (groverArcCoin V) (arcFlipFlop V)) :=
  groverDiscriminant_spec G hV hD hlam

/-- **Grover-walk 2×2 block correspondence.**  Every eigenvalue `μ` of `groverStep`
is `exp(s·i·θ)` for a sign `s` and an angle `θ ∈ [0, π]` with `cos θ = λ`, where
`λ ∈ [-1,1]` is an eigenvalue of the Jordan discriminant `D₀ = ½(SC + CS)`.

Derived sorry-free from `groverStep_discriminant_eigenvalue` by taking
`θ := arccos λ ∈ [0, π]` with `cos θ = λ` (`Real.cos_arccos`).  Pure trigonometric
bookkeeping over the genuine block decomposition. -/
theorem groverStep_block_correspondence (μ : ℂ)
    (hμ : μ ∈ spectrum ℂ (groverStep V)) :
    ∃ (lam : ℝ) (θ : ℝ) (s : Bool),
      lam ∈ Set.Icc (-1 : ℝ) 1 ∧
      θ ∈ Set.Icc (0 : ℝ) Real.pi ∧
      Real.cos θ = lam ∧
      (lam : ℂ) ∈ spectrum ℂ
        (Graphplay.ForMathlib.reflStepDiscriminant (groverArcCoin V) (arcFlipFlop V)) ∧
      μ = Complex.exp ((if s then 1 else -1) * Complex.I * θ) := by
  obtain ⟨lam, s, hlam, hspec, hμeq⟩ := groverStep_discriminant_eigenvalue μ hμ
  refine ⟨lam, Real.arccos lam, s, hlam, ⟨Real.arccos_nonneg lam, Real.arccos_le_pi lam⟩, ?_,
    hspec, hμeq⟩
  exact Real.cos_arccos hlam.1 hlam.2

theorem groverStep_spectrum (μ : ℂ)
    (hμ : μ ∈ spectrum ℂ (groverStep V)) :
    ∃ (lam : ℝ) (s : Bool),
      lam ∈ Set.Icc (-1 : ℝ) 1 ∧
      (lam : ℂ) ∈ spectrum ℂ
        (Graphplay.ForMathlib.reflStepDiscriminant (groverArcCoin V) (arcFlipFlop V)) ∧
      μ = Complex.exp ((if s then 1 else -1) * Complex.I * Real.arccos lam) := by
  -- Derived sorry-free from the single deep input `groverStep_block_correspondence`:
  -- it supplies the rotation angle `θ ∈ [0, π]` with `cos θ = λ`, and `arccos_cos`
  -- rewrites `θ = arccos λ`, giving the `exp(±i·arccos λ)` form.
  obtain ⟨lam, θ, s, hlam, ⟨hθ0, hθpi⟩, hcos, hspec, hμeq⟩ :=
    groverStep_block_correspondence μ hμ
  refine ⟨lam, s, hlam, hspec, ?_⟩
  have harc : Real.arccos lam = θ := by
    rw [← hcos, Real.arccos_cos hθ0 hθpi]
  rw [hμeq, harc]

/-! ## §6 Discrete-time equitable-partition / automorphism quotient

A graph automorphism — or, more generally, an equitable partition — reduces the
coined walk to a coined walk on the quotient, exactly as a graph automorphism
reduces the CTQW (cf. `Graphplay.EquitablePartition.pst_lift` and
`Graphplay.dtqw_equitable_lift`).  We model the automorphism case directly: a
permutation of the vertices preserving the (weighted) adjacency lifts to a
permutation of the arc space that **commutes with the one-step walk operator**,
so the walk descends to the quotient by the automorphism. -/

/-- A **graph automorphism** of a weighted graph: a vertex permutation that
preserves the adjacency matrix entrywise.  (Self-contained here to avoid
coupling.) -/
structure GraphAut (G : WeightedGraph V) where
  /-- The underlying vertex permutation. -/
  perm : Equiv.Perm V
  /-- It preserves the (Hermitian) adjacency matrix. -/
  preserves_adj : ∀ x y, G.adj (perm x) (perm y) = G.adj x y

/-- The **arc-space permutation matrix** induced by a vertex permutation `σ`:
`|x, y⟩ ↦ |σ x, σ y⟩`.  Entry `((x,y),(x',y'))` is `1` iff
`(x', y') = (σ x, σ y)`. -/
def arcPermMatrix (σ : Equiv.Perm V) : Matrix (V × V) (V × V) ℂ :=
  fun p q => if q = (σ p.1, σ p.2) then 1 else 0

/-- Left-multiplication by `arcPermMatrix σ` selects the `(σ p.1, σ p.2)`-row:
`(arcPermMatrix σ * M) p q = M (σ p.1, σ p.2) q`. -/
theorem arcPermMatrix_mul_apply (σ : Equiv.Perm V)
    (M : Matrix (V × V) (V × V) ℂ) (p q : V × V) :
    (arcPermMatrix σ * M) p q = M (σ p.1, σ p.2) q := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (σ p.1, σ p.2)]
  · simp [arcPermMatrix]
  · intro r _ hr
    simp only [arcPermMatrix]
    rw [if_neg hr, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Right-multiplication by `arcPermMatrix σ` selects the
`(σ⁻¹ q.1, σ⁻¹ q.2)`-column: `(M * arcPermMatrix σ) p q = M p (σ⁻¹ q.1, σ⁻¹ q.2)`. -/
theorem arcPermMatrix_mul_apply' (σ : Equiv.Perm V)
    (M : Matrix (V × V) (V × V) ℂ) (p q : V × V) :
    (M * arcPermMatrix σ) p q = M p (σ⁻¹ q.1, σ⁻¹ q.2) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (σ⁻¹ q.1, σ⁻¹ q.2)]
  · simp only [arcPermMatrix]
    rw [if_pos (by simp), mul_one]
  · intro r _ hr
    simp only [arcPermMatrix]
    rw [if_neg ?_, mul_zero]
    intro h; apply hr
    rw [h]; ext <;> simp
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Diagonally-invariant matrices commute with the arc permutation.**  If a
matrix `M` on the arc space is invariant under the diagonal action of `σ`
(`M (σ a, σ b) (σ c, σ d) = M (a, b) (c, d)`), then it commutes with
`arcPermMatrix σ`. -/
theorem arcPermMatrix_comm_of_invariant (σ : Equiv.Perm V)
    (M : Matrix (V × V) (V × V) ℂ)
    (hM : ∀ a b c d : V, M (σ a, σ b) (σ c, σ d) = M (a, b) (c, d)) :
    arcPermMatrix σ * M = M * arcPermMatrix σ := by
  ext p q
  rw [arcPermMatrix_mul_apply, arcPermMatrix_mul_apply']
  -- `M (σ p.1, σ p.2) q = M p (σ⁻¹ q.1, σ⁻¹ q.2)`.
  have h := hM p.1 p.2 (σ⁻¹ q.1) (σ⁻¹ q.2)
  have e1 : σ (σ⁻¹ q.1) = q.1 := by
    rw [Equiv.Perm.inv_def]; exact σ.apply_symm_apply q.1
  have e2 : σ (σ⁻¹ q.2) = q.2 := by
    rw [Equiv.Perm.inv_def]; exact σ.apply_symm_apply q.2
  rw [e1, e2] at h
  rw [← h]

/-- The flip-flop shift is diagonally `σ`-invariant. -/
theorem arcFlipFlop_invariant (σ : Equiv.Perm V) (a b c d : V) :
    arcFlipFlop V (σ a, σ b) (σ c, σ d) = arcFlipFlop V (a, b) (c, d) := by
  simp only [arcFlipFlop]
  congr 1
  simp [σ.injective.eq_iff]

omit [Fintype V] in
/-- The arc coin built from a vertex-independent (constant-on-equality) coin is
diagonally `σ`-invariant, when the per-vertex coin `coin` is itself
`σ`-invariant: `coin (σ b) (σ d) = coin b d`. -/
theorem arcCoin_invariant (σ : Equiv.Perm V) (coin : Matrix V V ℂ)
    (hcoin : ∀ b d : V, coin (σ b) (σ d) = coin b d) (a b c d : V) :
    arcCoin coin (σ a, σ b) (σ c, σ d) = arcCoin coin (a, b) (c, d) := by
  simp only [arcCoin, σ.injective.eq_iff, hcoin]

/-- The Grover coin is `σ`-invariant (it depends only on equality of indices). -/
theorem groverCoin_invariant (σ : Equiv.Perm V) (b d : V) :
    groverCoin V (σ b) (σ d) = groverCoin V b d := by
  simp only [groverCoin, σ.injective.eq_iff]

/-- **Automorphism quotient for the coined walk (discrete-time analogue of the
equitable-partition lift).**  A graph automorphism `φ` of `G` lifts to an
arc-space permutation `Φ := arcPermMatrix φ.perm` that *commutes* with the
Grover walk one-step operator: `Φ · U = U · Φ`.  Consequently the walk descends
to the quotient by `⟨φ⟩` (the cell-uniform / orbit subspaces are invariant and
the restriction is the coined walk of the quotient graph).

This is the discrete-time avatar of the Bachman–Tamon equitable-partition
lifting (arXiv:1108.0339) and matches `Graphplay.dtqw_equitable_lift`.

Reference: Portugal (2018), §10.3; Bachman–Tamon, arXiv:1108.0339. -/
theorem grover_walk_commutes_with_automorphism (G : WeightedGraph V)
    (φ : GraphAut G) :
    arcPermMatrix φ.perm * groverStep V = groverStep V * arcPermMatrix φ.perm := by
  -- The flip-flop and the Grover arc coin are each diagonally `φ`-invariant,
  -- hence each commutes with `Φ`; therefore so does their product `U = S · C`.
  unfold groverStep groverArcCoin
  set σ := φ.perm
  have hS : arcPermMatrix σ * arcFlipFlop V = arcFlipFlop V * arcPermMatrix σ :=
    arcPermMatrix_comm_of_invariant σ _ (arcFlipFlop_invariant σ)
  have hC : arcPermMatrix σ * arcCoin (groverCoin V)
      = arcCoin (groverCoin V) * arcPermMatrix σ :=
    arcPermMatrix_comm_of_invariant σ _
      (arcCoin_invariant σ (groverCoin V) (groverCoin_invariant σ))
  calc arcPermMatrix σ * (arcFlipFlop V * arcCoin (groverCoin V))
      = (arcPermMatrix σ * arcFlipFlop V) * arcCoin (groverCoin V) := by
          rw [Matrix.mul_assoc]
    _ = (arcFlipFlop V * arcPermMatrix σ) * arcCoin (groverCoin V) := by rw [hS]
    _ = arcFlipFlop V * (arcPermMatrix σ * arcCoin (groverCoin V)) := by
          rw [Matrix.mul_assoc]
    _ = arcFlipFlop V * (arcCoin (groverCoin V) * arcPermMatrix σ) := by rw [hC]
    _ = (arcFlipFlop V * arcCoin (groverCoin V)) * arcPermMatrix σ := by
          rw [Matrix.mul_assoc]

/-- **Coined-walk quotient predicate.**  The coined walk on `G` *reduces* to a
quotient under an automorphism `φ` when the lifted arc permutation commutes with
the step operator (so the walk restricts to each `φ`-invariant subspace).  This
packages `grover_walk_commutes_with_automorphism` as a reusable predicate. -/
def ReducesUnderAut (G : WeightedGraph V) (φ : GraphAut G) : Prop :=
  arcPermMatrix φ.perm * groverStep V = groverStep V * arcPermMatrix φ.perm

/-- The Grover walk always reduces under any automorphism (restatement of the
commutation theorem as the predicate). -/
theorem reducesUnderAut_of_automorphism (G : WeightedGraph V) (φ : GraphAut G) :
    ReducesUnderAut G φ :=
  grover_walk_commutes_with_automorphism G φ

end CoinedWalk
end Graphplay
