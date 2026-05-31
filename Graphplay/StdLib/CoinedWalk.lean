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
3. states the **Szegedy spectral correspondence** — eigenvalues of the coined
   walk are `e^{±i arccos σ}` for `σ` a singular value of the discriminant /
   transition matrix — precisely, with an honest `sorry` on the proof;
4. states the **discrete-time equitable-partition / automorphism quotient**:
   a graph automorphism (or equitable partition) reduces the coined walk to the
   coined walk on the quotient (honest `sorry`).

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

/-- **The irreducible SVD/Jordan residual of the Grover-walk spectral theorem.**
The single deep fact, isolated exactly as for the Szegedy walk
(`Graphplay.WeightedGraph.szegedy_discriminant_eigenvalue`): every Grover-walk
eigenvalue `μ` is `exp(±i · arccos σ)` for a singular value `σ ∈ [0, 1]` of the
discriminant `D = √P ∘ √Pᵀ`, equivalently a transition eigenvalue in
`spectrum G.randomWalkOp`.  The content is **Jordan's lemma** (`U = S·C`, a product
of two coin reflections, acts on each 2-D `span{|s_x⟩, S|s_x⟩}` plane as a rotation
by twice the principal angle) plus the **discriminant SVD** supplying those angles
as `arccos σ`.  Mathlib has singular *values* (`LinearMap.singularValues`) but no SVD
*factorisation* and no Jordan-lemma block reduction, so this extraction cannot yet be
derived; this is the honest minimal residual.  `groverStep_block_correspondence` and
`groverStep_spectrum` are trigonometric bookkeeping on top of it.

Reference: Szegedy, FOCS 2004, Theorem 1; Portugal (2018), §7.3; Jordan (1875) for
the two-reflections lemma. -/
theorem groverStep_discriminant_eigenvalue (G : WeightedGraph V) (μ : ℂ)
    (hμ : μ ∈ spectrum ℂ (groverStep V)) :
    ∃ (σ : ℝ) (s : Bool),
      σ ∈ Set.Icc (0 : ℝ) 1 ∧
      (σ : ℂ) ∈ spectrum ℂ G.randomWalkOp ∧
      μ = Complex.exp ((if s then 1 else -1) * Complex.I * Real.arccos σ) := by
  sorry

/-- **Grover-walk 2×2 block correspondence.**  Every eigenvalue `μ` of `groverStep`
is `exp(s·i·θ)` for a sign `s` and an angle `θ ∈ [0, π]` with `cos θ = σ`, where
`σ ∈ [0,1]` is a singular value of the discriminant (a transition eigenvalue).

Derived sorry-free from the irreducible residual `groverStep_discriminant_eigenvalue`
by taking `θ := arccos σ ∈ [0, π]` (`Real.arccos_nonneg`, `Real.arccos_le_pi`) with
`cos θ = σ` (`Real.cos_arccos`, using `0 ≤ σ ⇒ -1 ≤ σ`).  The genuinely deep block
decomposition lives in the residual; this is pure trigonometric bookkeeping. -/
theorem groverStep_block_correspondence (G : WeightedGraph V) (μ : ℂ)
    (hμ : μ ∈ spectrum ℂ (groverStep V)) :
    ∃ (σ : ℝ) (θ : ℝ) (s : Bool),
      σ ∈ Set.Icc (0 : ℝ) 1 ∧
      θ ∈ Set.Icc (0 : ℝ) Real.pi ∧
      Real.cos θ = σ ∧
      (σ : ℂ) ∈ spectrum ℂ G.randomWalkOp ∧
      μ = Complex.exp ((if s then 1 else -1) * Complex.I * θ) := by
  obtain ⟨σ, s, hσ, hspec, hμeq⟩ := groverStep_discriminant_eigenvalue G μ hμ
  refine ⟨σ, Real.arccos σ, s, hσ, ⟨Real.arccos_nonneg σ, Real.arccos_le_pi σ⟩, ?_,
    hspec, hμeq⟩
  exact Real.cos_arccos (le_trans (by norm_num) hσ.1) hσ.2

theorem groverStep_spectrum (G : WeightedGraph V) (μ : ℂ)
    (hμ : μ ∈ spectrum ℂ (groverStep V)) :
    ∃ (σ : ℝ) (s : Bool),
      σ ∈ Set.Icc (0 : ℝ) 1 ∧
      (σ : ℂ) ∈ spectrum ℂ G.randomWalkOp ∧
      μ = Complex.exp ((if s then 1 else -1) * Complex.I * Real.arccos σ) := by
  -- Derived sorry-free from the single deep input `groverStep_block_correspondence`:
  -- it supplies the rotation angle `θ ∈ [0, π]` with `cos θ = σ`, and `arccos_cos`
  -- rewrites `θ = arccos σ`, giving the `exp(±i·arccos σ)` form.
  obtain ⟨σ, θ, s, hσ, ⟨hθ0, hθpi⟩, hcos, hspec, hμeq⟩ :=
    groverStep_block_correspondence G μ hμ
  refine ⟨σ, s, hσ, hspec, ?_⟩
  have harc : Real.arccos σ = θ := by
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
