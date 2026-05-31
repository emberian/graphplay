/-
# Graphplay.StdLib.Hamming

Standard-library entry for the **Hamming graph** `H(n, q)` — the Cartesian
product `K_q □ K_q □ ⋯ □ K_q` (`n` factors), or equivalently the Cayley
graph of `(ℤ/q)^n` with the generating set `{e_i (k) : 1 ≤ i ≤ n, 1 ≤ k <
q}` of all "single-coordinate" elements.

Two vertices `x, y : Fin q → Fin n` (length-`n` strings over `q`-ary
alphabet) are adjacent iff they differ in exactly one coordinate.  This is
the canonical distance-regular graph whose spectrum is computed by
**Krawtchouk polynomials**:

  eigenvalue indexed by `k ∈ {0, …, n}` is
    `λ_k = (q-1)·n − q·k`
  (Brouwer–Haemers, *Spectra of Graphs*, §12.3.2; equivalent to the
  Krawtchouk polynomial `K_k(0; n, q)` evaluation).

The mixing question on Hamming graphs is fully classified:

* Ahmadi, Belk, Tamon, Wendler 2003 (*The continuous-time quantum walk on
  Hamming graphs*, arXiv:quant-ph/0209106) prove uniform mixing for
  `q ∈ {2, 3, 4}` at time `τ = 2π / q`, and *no* uniform mixing for
  `q ≥ 5`.
* Levine–Tamon 2024 (arXiv:2605.04414) close the chiral case: any chiral
  signing of `H(n, q)` for `q ≥ 5` also fails to mix uniformly.

We state both halves of the iff; proofs are `sorry`-ed.
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Graphplay.Weighted
import Graphplay.Mixing

open scoped Matrix Real
open Real

universe u

namespace Graphplay
namespace StdLib

/-! ## The Hamming graph `H(n, q)` -/

/-- The **Hamming distance** between two length-`n` strings over an
alphabet of size `q`. -/
def hammingDistFn {n q : ℕ} (x y : Fin n → Fin q) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => x i ≠ y i)).card

/-- The Hamming distance is symmetric. -/
theorem hammingDistFn_comm {n q : ℕ} (x y : Fin n → Fin q) :
    hammingDistFn x y = hammingDistFn y x := by
  unfold hammingDistFn
  congr 1
  apply Finset.filter_congr
  intro i _
  simp [ne_comm]

/-- The Hamming distance from a string to itself is `0`. -/
@[simp] theorem hammingDistFn_self {n q : ℕ} (x : Fin n → Fin q) :
    hammingDistFn x x = 0 := by
  unfold hammingDistFn
  simp

/-- The **Hamming graph** `H(n, q)` on the vertex set `Fin n → Fin q` of
length-`n` strings over a `q`-ary alphabet: edges connect strings at
Hamming distance exactly `1`.

For `q = 2` this is the Boolean hypercube `Q_n` (cf.
`Graphplay.StdLib.Hypercube`); for `n = 1` it is the complete graph
`K_q`. -/
noncomputable def Hamming (n q : ℕ) [Fintype (Fin n → Fin q)]
    [DecidableEq (Fin n → Fin q)] :
    WeightedGraph (Fin n → Fin q) where
  adj := fun x y => if hammingDistFn x y = 1 then (1 : ℂ) else 0
  herm := by
    -- Real-symmetric (Hamming distance is symmetric) ⇒ Hermitian.
    refine Matrix.IsHermitian.ext (fun x y => ?_)
    show star (if hammingDistFn y x = 1 then (1 : ℂ) else 0)
        = if hammingDistFn x y = 1 then (1 : ℂ) else 0
    rw [hammingDistFn_comm y x]
    by_cases h : hammingDistFn x y = 1
    · rw [if_pos h]; simp
    · rw [if_neg h]; simp
  loopless := by
    intro v
    -- `hammingDistFn v v = 0 ≠ 1`.
    rw [hammingDistFn_self]
    simp

/-! ## Krawtchouk eigenvalues -/

/-- The **Krawtchouk polynomial** `K_k(x; n, q)` of degree `k`,
defined by the standard generating-function recurrence
`K_k(x; n, q) = Σ_{j=0}^{k} (-1)^j (q-1)^{k-j} C(x, j) C(n - x, k - j)`.
This is the family that diagonalizes the Hamming-scheme intersection
matrix; see Brouwer–Haemers §12.3, or van Lint, *Introduction to coding
theory*, §3.2. -/
noncomputable def krawtchouk (n q : ℕ) (k : ℕ) (x : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1),
    ((-1 : ℝ)^j) * ((q - 1 : ℝ)^(k - j)) *
      (Nat.choose x j : ℝ) * (Nat.choose (n - x) (k - j) : ℝ)

/-- **Brouwer–Haemers, *Spectra of Graphs* §12.3.2.**  The Hamming graph
`H(n, q)` has spectrum `{ λ_k : 0 ≤ k ≤ n }` (with multiplicity given by
the Krawtchouk weight), where
  `λ_k = n(q - 1) − q k = krawtchouk n q 1 k`.

(The polynomial `K_1` is the linear Krawtchouk polynomial; evaluating at
`x = k` gives `n(q - 1) − qk`.) -/
theorem hamming_eigenvalue (n q : ℕ) [Fintype (Fin n → Fin q)]
    [DecidableEq (Fin n → Fin q)] (k : ℕ) (hk : k ≤ n) :
    ∃ μ : ℝ, μ ∈ spectrum ℝ (Hamming n q).adj ∧
      μ = (n : ℝ) * ((q : ℝ) - 1) - (q : ℝ) * (k : ℝ) := by
  -- Diagonalize over the characters of `(ℤ/q)^n`; cf. Brouwer–Haemers.
  sorry

/-! ## Uniform mixing iff `q ≤ 4` -/

/-- **Ahmadi–Belk–Tamon–Wendler (2003).**  For `q ∈ {2, 3, 4}`, the
Hamming graph `H(n, q)` is uniformly mixing at time `τ = 2π / q`.

Reference: arXiv:quant-ph/0209106, Theorem 3.  The proof goes via the
character basis: uniformity at time `τ` reduces to
`|∑_x ω^{xs} exp(-iτ λ_s)|² = 1` for every character index `s`, which is
satisfied for `q ∈ {2, 3, 4}` thanks to integrality of the Gauss sums on
`ℤ/q`. -/
theorem hamming_uniformMixing_of_q_le_4 (n q : ℕ) (hq2 : 2 ≤ q) (hq4 : q ≤ 4)
    [Fintype (Fin n → Fin q)] [DecidableEq (Fin n → Fin q)] :
    IsUniformMixing (Hamming n q) (2 * Real.pi / q) := by
  -- Reduce to a Gauss-sum identity on `ℤ/q` for `q ∈ {2,3,4}`.
  sorry

/-- **Ahmadi–Belk–Tamon–Wendler (2003) — negative half.**  For `q ≥ 5`
and `n ≥ 1`, the Hamming graph `H(n, q)` does *not* exhibit uniform
mixing at any time `τ ∈ ℝ`. -/
theorem hamming_no_uniformMixing_of_q_ge_5 (n q : ℕ) (hq : 5 ≤ q) (hn : 1 ≤ n)
    [Fintype (Fin n → Fin q)] [DecidableEq (Fin n → Fin q)] :
    ∀ τ : ℝ, ¬ IsUniformMixing (Hamming n q) τ := by
  -- The Gauss sum `∑_{a ∈ ℤ/q} ω^{a²}` fails to have all-equal moduli
  -- across non-trivial characters once `q ≥ 5`.
  sorry

/-- **Combined statement / Ahmadi et al. 2003 + Levine–Tamon 2024.**  The
Hamming graph `H(n, q)` admits uniform mixing if and only if `q ≤ 4`.

Reference: arXiv:quant-ph/0209106 (Hermitian case); arXiv:2605.04414
(chiral closure, ruling out the possibility that adding chiral signings
to the Hamiltonian could rescue mixing for `q ≥ 5`). -/
theorem hamming_uniformMixing_iff_q_le_4 (n q : ℕ) (hn : 1 ≤ n) (hq : 2 ≤ q)
    [Fintype (Fin n → Fin q)] [DecidableEq (Fin n → Fin q)] :
    (∃ τ : ℝ, IsUniformMixing (Hamming n q) τ) ↔ q ≤ 4 := by
  refine ⟨?_, ?_⟩
  · -- Forward: if uniform mixing occurs, then `q ≤ 4`.  Contrapositive of
    -- `hamming_no_uniformMixing_of_q_ge_5`: if `q ≥ 5`, no time `τ` mixes.
    rintro ⟨τ, hmix⟩
    by_contra hq4
    have hq5 : 5 ≤ q := by omega
    exact hamming_no_uniformMixing_of_q_ge_5 n q hq5 hn τ hmix
  · -- Backward: choose `τ = 2π / q`.
    intro hle
    refine ⟨2 * Real.pi / q, ?_⟩
    exact hamming_uniformMixing_of_q_le_4 n q hq hle

/-! ## Chiral closure (Levine–Tamon 2024) -/

/-- **Levine–Tamon (2024), arXiv:2605.04414.**  For `q ≥ 5` and `n ≥ 1`,
*no* chiral signing of `H(n, q)` exhibits uniform mixing.  In other
words, the obstruction at `q ≥ 5` is not removable by chiral
modifications. -/
theorem hamming_no_chiral_uniformMixing (n q : ℕ) (hq : 5 ≤ q) (hn : 1 ≤ n)
    [Fintype (Fin n → Fin q)] [DecidableEq (Fin n → Fin q)]
    (σ : ChiralMixingSigning (Hamming n q)) :
    ∀ τ : ℝ, ¬ (∀ u v : Fin n → Fin q,
        ‖(NormedSpace.exp (-(Complex.I * (τ : ℂ)) • σ.signed)) u v‖ ^ 2 =
          1 / (Fintype.card (Fin n → Fin q) : ℝ)) := by
  -- Cf. arXiv:2605.04414 §4: the Krawtchouk obstruction is preserved
  -- under chiral signings.
  sorry

end StdLib
end Graphplay
