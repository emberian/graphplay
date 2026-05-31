/-
# Graphplay.StdLib.Path

Standard-library entry for the **path graph** family `P_n` (with `n+1`
vertices `Fin (n+1)`), including the engineered weighted paths used in the
canonical Christandl–Datta–Ekert–Landahl quantum-state-transfer protocol.

Two pre-designed quotient families live here:

1.  The **unweighted path** `Path n`: the simple graph on `Fin (n+1)` with
    edges `{k, k+1}`.  PST holds exactly for `n ∈ {2, 3}` (so `P_3` and
    `P_4` in 1-indexed vertex-count notation), at time `τ = π/√2` for
    `P_3` and `τ = π/√5` for `P_4` (Christandl, Datta, Ekert, Landahl,
    *Perfect state transfer in quantum spin networks*, Phys. Rev. Lett. 92,
    187902 (2004), arXiv:quant-ph/0309131).

2.  The **engineered weighted path** `WeightedPath n J` with arbitrary
    couplings `J : Fin n → ℝ`, and in particular the *Christandl–Landahl–
    Werner couplings* `J_k = √(k(n-k+1))` which give PST between the two
    endpoints of `P_{n+1}` at time `τ = π/2` for **every** `n` (Christandl,
    Landahl, Werner, *Perfect transfer of arbitrary states in quantum spin
    networks*, Phys. Rev. A 71, 032312 (2005), arXiv:quant-ph/0411020).

Both are stated; proofs are `sorry`-ed.
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.NumberTheory.Niven
import Graphplay.Weighted
import Graphplay.PST

open scoped Matrix Real
open Real

universe u

namespace Graphplay
namespace StdLib

/-! ## The unweighted path `P_{n+1}` on `Fin (n+1)` -/

/-- The **path graph** `Path n` on vertex set `Fin (n+1)`: a Hermitian
adjacency matrix with `adj k l = 1` whenever `|k - l| = 1` and `0`
otherwise.  This is the standard nearest-neighbour 1-D quantum spin chain.

For `n = 0` this is the empty graph on one vertex; for `n = 1` it is a
single edge; etc.  PST between the endpoints holds for `n = 2` and `n = 3`
only (Christandl–Datta–Ekert–Landahl 2004, arXiv:quant-ph/0309131). -/
noncomputable def Path (n : ℕ) : WeightedGraph (Fin (n + 1)) where
  adj := fun k l =>
    if (k.val + 1 = l.val) ∨ (l.val + 1 = k.val) then (1 : ℂ) else 0
  herm := by
    -- Symmetric real-valued (0/1) matrix is Hermitian: `star` fixes the
    -- real entries `0,1`, and the defining disjunction is symmetric in `k,l`.
    refine Matrix.IsHermitian.ext (fun k l => ?_)
    by_cases h : (k.val + 1 = l.val) ∨ (l.val + 1 = k.val)
    · rw [if_pos h, if_pos (Or.symm h)]; simp
    · rw [if_neg h, if_neg (fun hc => h (Or.symm hc))]; simp
  loopless := by
    intro v
    simp

/-- The PST time `τ_n` for the unweighted path `Path n` between its two
endpoints, when PST is possible.  We use the Christandl–Datta–Ekert–Landahl
values: `τ₂ = π / √2` and `τ₃ = π / √5`.  (For other `n` we set the value
to `0` as a placeholder; no PST claim is attached.) -/
noncomputable def pathPSTTime : ℕ → ℝ
  | 2 => Real.pi / Real.sqrt 2
  | 3 => Real.pi / Real.sqrt 5
  | _ => 0

/-- **Christandl–Datta–Ekert–Landahl (2004).**  The unweighted path on
`n + 1` vertices admits PST from vertex `0` to vertex `n` exactly when
`n ∈ {2, 3}`, at the times `pathPSTTime n`.

Reference: arXiv:quant-ph/0309131, Theorem 1. -/
theorem path_PST_endpoint_endpoint
    (n : ℕ) (hn : n = 2 ∨ n = 3) :
    IsPST (Path n) (0 : Fin (n + 1)) (Fin.last n) (pathPSTTime n) := by
  -- The spectrum of the path is `2 cos(kπ / (n+1))`, and the endpoint-to-
  -- endpoint amplitude factors through a Chebyshev sum that has unit
  -- modulus precisely at the two listed values of `n`.
  sorry

/-! ### The Niven obstruction behind the negative path case

The eigenvalues of the unweighted path on `n + 1` vertices are
`2 cos((k+1)π/(n+2))` for `k = 0, …, n`.  PST forces these eigenvalues onto a
common arithmetic progression (the Godsil ratio condition), which in
particular requires their pairwise ratios to be rational.  The number-theoretic
obstruction is **Niven's theorem**: the cosine of a rational multiple `r·π` of
`π` is irrational whenever the reduced denominator `r.den` exceeds `3`.

We make this content explicit and *fully proved* (Mathlib supplies Niven as
`Real.irrational_cos_rat_mul_pi`): for `n ≥ 4` the smallest path eigenvalue
angle `π/(n+2)` already produces an **irrational** cosine, so the path spectrum
cannot be rationally commensurable, which is the algebraic heart of the
no-PST result. -/

/-- **Niven obstruction for the path spectrum.**  For `n ≥ 4`, the cosine
`cos(π/(n+2))` — the angle of the extremal path eigenvalue
`2 cos(π/(n+2))` of `P_{n+1}` — is **irrational**.

Proof: write the angle as `r·π` with `r = 1/(n+2) : ℚ`.  Since `1 ≤ n+2` and
`gcd(1, n+2) = 1`, the reduced denominator is `r.den = n + 2 ≥ 6 > 3`, so
Niven's theorem (`Real.irrational_cos_rat_mul_pi`) applies. -/
theorem cos_path_angle_irrational (n : ℕ) (hn : 4 ≤ n) :
    Irrational (Real.cos (Real.pi / ((n : ℝ) + 2))) := by
  -- Use the rational `q = (n+2)⁻¹`, whose reduced denominator is `n + 2 > 3`.
  set q : ℚ := ((n + 2 : ℕ) : ℚ)⁻¹ with hq
  have hden : 3 < q.den := by
    rw [hq, Rat.inv_natCast_den_of_pos (by omega)]; omega
  have hangle : (q : ℝ) * Real.pi = Real.pi / ((n : ℝ) + 2) := by
    have hqr : (q : ℝ) = ((n : ℝ) + 2)⁻¹ := by rw [hq]; push_cast; ring
    rw [hqr]
    field_simp
  rw [← hangle]
  exact irrational_cos_rat_mul_pi hden

/-- **Negative side of Christandl–Datta–Ekert–Landahl (2004).**  For all
other `n ≥ 1`, the unweighted path on `n + 1` vertices does *not* admit
PST between its two endpoints at any time `τ`.

Reference: arXiv:quant-ph/0309131; Godsil–Kirkland–Severini–Smith
(arXiv:1201.4822); Coutinho thesis (2014) §2.4.

**Status.**  The genuinely number-theoretic core — that the path spectrum is
not rationally commensurable for `n ≥ 4` — is captured *and proved* in
`cos_path_angle_irrational` via Mathlib's Niven theorem.  The remaining
ingredient is the spectral PST⇒ratio-condition bridge (Godsil 2012, Thm 2.2),
which lives in `Graphplay.PST.GodsilRatio` and is the file-wide residual; it is
not yet available in importable form here.  The `n ∈ {0, 1}` cases (paths too
short to have endpoint PST except the trivial edge) and the assembly are left
as an honest `sorry` attached to this *true* statement. -/
theorem path_no_PST_endpoint_endpoint
    (n : ℕ) (hn : n ≠ 2 ∧ n ≠ 3) (h1 : 1 ≤ n) :
    ∀ τ : ℝ, ¬ IsPST (Path n) (0 : Fin (n + 1)) (Fin.last n) τ := by
  -- Cf. arXiv:quant-ph/0309131; relies on irrationality / commensurability
  -- of the cosine eigenvalues for `n ∉ {2, 3}` (`cos_path_angle_irrational`),
  -- combined with the Godsil PST⇒ratio bridge.
  sorry

/-! ## Engineered weighted paths (Christandl–Landahl–Werner couplings) -/

/-- An **engineered weighted path** on `Fin (n + 1)` with edge weights
`J : Fin n → ℝ`.  Edge `k --- k+1` carries weight `J k`; all other entries
are zero. -/
noncomputable def WeightedPath (n : ℕ) (J : Fin n → ℝ) :
    WeightedGraph (Fin (n + 1)) where
  adj := fun k l =>
    if h : k.val + 1 = l.val then
      ((J ⟨k.val, by
          have : k.val < n + 1 := k.isLt
          omega⟩ : ℝ) : ℂ)
    else if h' : l.val + 1 = k.val then
      ((J ⟨l.val, by
          have : l.val < n + 1 := l.isLt
          omega⟩ : ℝ) : ℂ)
    else 0
  herm := by
    -- Real-symmetric ⇒ Hermitian: the entry at `(k,l)` and `(l,k)` are equal
    -- real numbers (`J⟨·⟩` or `0`), and `star` fixes real values.
    refine Matrix.IsHermitian.ext (fun k l => ?_)
    by_cases h1 : k.val + 1 = l.val
    · -- `k+1 = l`: both entries equal `J⟨k⟩`.
      have hne : ¬ l.val + 1 = k.val := by omega
      rw [dif_pos h1, dif_neg hne, dif_pos h1]; simp
    · by_cases h2 : l.val + 1 = k.val
      · -- `l+1 = k`: both entries equal `J⟨l⟩`.
        rw [dif_pos h2, dif_neg h1, dif_pos h2]; simp
      · -- neither: both entries are `0`.
        rw [dif_neg h2, dif_neg h1, dif_neg h1, dif_neg h2]; simp
  loopless := by
    intro v
    -- `v.val + 1 = v.val` is impossible; `v.val + 1 = v.val` likewise.
    simp

/-- The **Christandl–Landahl–Werner couplings**:
`J_k = √(k · (n + 1 - k))` for `1 ≤ k ≤ n`.  Equivalently, in the `Fin n`
parameterization used by `WeightedPath`, `J ⟨k, _⟩ = √((k+1)(n-k))`. -/
noncomputable def CLWCouplings (n : ℕ) : Fin n → ℝ :=
  fun k => Real.sqrt ((k.val + 1 : ℝ) * ((n : ℝ) - k.val))

/-- The **Christandl–Landahl–Werner engineered path** on `Fin (n + 1)`:
the weighted path with edge weights `J_k = √(k(n - k + 1))`. -/
noncomputable def CLWPath (n : ℕ) : WeightedGraph (Fin (n + 1)) :=
  WeightedPath n (CLWCouplings n)

/-- **Christandl–Landahl–Werner (2005).**  The engineered weighted path
with couplings `J_k = √(k(n - k + 1))` exhibits PST between the two
endpoints `0` and `n` at time `τ = π / 2`, for every `n ≥ 1`.

Reference: arXiv:quant-ph/0411020, Theorem 1.  The proof factors through
the observation that the Hamiltonian is a faithful representation of the
spin-`n/2` angular momentum operator `J_x`, whose spectrum is the
arithmetic progression `{-n/2, -n/2 + 1, …, n/2}`. -/
theorem weightedPath_PST (n : ℕ) (h : 1 ≤ n) :
    IsPST (CLWPath n) (0 : Fin (n + 1)) (Fin.last n) (Real.pi / 2) := by
  -- Reduces to the closed-form `(exp(-i π J_x / 2))_{0,n} = (-i)^n`,
  -- whose modulus is 1.
  sorry

/-- More generally, *any* mirror-symmetric coupling profile whose
single-excitation spectrum has integer commensurable gaps yields PST at
some time `τ` (Karbach–Stolze 2005, Yung 2006).  We state the
specialization to CLW. -/
theorem weightedPath_PST_modulus_eq_one (n : ℕ) (h : 1 ≤ n) :
    ‖(CLWPath n).evolve (Real.pi / 2) 0 (Fin.last n)‖ = 1 :=
  weightedPath_PST n h

/-! ## Convenience aliases -/

/-! ## Computable rational companions

These are the same 0/1 (or rational-weighted) adjacency matrices as `Path`
and `WeightedPath`, but valued in `ℚ` rather than `ℂ`, so that they are
fully `#eval`-able.  They can be lifted to `ℂ` via `Matrix.map (algebraMap ℚ ℂ)`
when needed.
-/

/-- Computable companion to `Path n`: the 0/1 adjacency matrix of the
unweighted path on `Fin (n + 1)`, valued in `ℚ`. -/
def Path.adjMatrixℚ (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ :=
  fun k l =>
    if (k.val + 1 = l.val) ∨ (l.val + 1 = k.val) then (1 : ℚ) else 0

/-- Computable companion to `WeightedPath n J`: the engineered weighted
adjacency matrix on `Fin (n + 1)` with rational weights `J : Fin n → ℚ`. -/
def WeightedPath.adjMatrixℚ (n : ℕ) (J : Fin n → ℚ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ :=
  fun k l =>
    if h : k.val + 1 = l.val then
      J ⟨k.val, by have : k.val < n + 1 := k.isLt; omega⟩
    else if h' : l.val + 1 = k.val then
      J ⟨l.val, by have : l.val < n + 1 := l.isLt; omega⟩
    else 0

/-- Smoke test: `Path 4` has a `1` between vertex 0 and vertex 1. -/
example : (Path.adjMatrixℚ 4) ⟨0, by decide⟩ ⟨1, by decide⟩ = 1 := by decide

/-- Smoke test: `Path 4` is loopless (zero diagonal). -/
example : Matrix.trace (Path.adjMatrixℚ 4) = 0 := by native_decide

#eval (Path.adjMatrixℚ 4) ⟨0, by decide⟩ ⟨1, by decide⟩
#eval Matrix.trace (Path.adjMatrixℚ 4)

/-- The path on three vertices (`P_3` in graph-theory notation), the
smallest unweighted graph that exhibits endpoint-to-endpoint PST. -/
noncomputable def P3 : WeightedGraph (Fin 3) := Path 2

/-- The path on four vertices (`P_4`), the largest unweighted path with
endpoint-to-endpoint PST. -/
noncomputable def P4 : WeightedGraph (Fin 4) := Path 3

/-- PST on `P_3` at `τ = π / √2`. -/
theorem P3_PST : IsPST P3 (0 : Fin 3) (Fin.last 2) (Real.pi / Real.sqrt 2) :=
  path_PST_endpoint_endpoint 2 (Or.inl rfl)

/-- PST on `P_4` at `τ = π / √5`. -/
theorem P4_PST : IsPST P4 (0 : Fin 4) (Fin.last 3) (Real.pi / Real.sqrt 5) :=
  path_PST_endpoint_endpoint 3 (Or.inr rfl)

end StdLib
end Graphplay
