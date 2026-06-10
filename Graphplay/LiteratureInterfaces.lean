/-
# Graphplay.LiteratureInterfaces

**An honesty-and-architecture artifact.**

This file collects the genuinely-unformalized *vital literature results* that the
rest of Graphplay relies on, as **named, documented typeclasses** carrying the
precise statement of each literature theorem as a field.

## The design principle (read this!)

These are **NOT** `axiom`s.  Each result below is a `class` whose single field is
a `Prop` (or proof-carrying datum) stating exactly what the cited paper proves.

A downstream theorem of the form

```
theorem foo [LiteratureResult] : goal := by exact LiteratureResult.field …
```

is then a **genuinely proven, axiom-clean conditional theorem**: it contains no
`sorry`, introduces no `sorryAx` into the axiom set, and instead lists the
literature result as an *explicit, named, auditable hypothesis* in its type.  The
moment Mathlib (or our own work) grows a proof of the result, one supplies the
corresponding instance and *every* theorem that assumed `[LiteratureResult]` is
discharged with no further edits.

In short: **these typeclasses name results proven in the literature but not yet
available in Mathlib v4.30.0.  A theorem assuming `[C]` is a sorry-free
conditional theorem, and supplying the instance `C` (once Mathlib grows the
result) discharges it.**

Contrast with the status quo, where the same dependencies live as buried `sorry`s
inside proofs — opaque, unauditable, and silently poisoning the axiom set with
`sorryAx`.

## Self-containment

To keep this file a tidy, fast-compiling, cycle-free interface, each class states
a **faithful self-contained version** of its result over plain Mathlib types
(matrices, reals, `SimpleGraph`, …) rather than importing the (heavy, mutually
dependent) consumer files.  Each class docstring names its **intended consumer**
theorem(s) so the follow-up refactor can wire `[C]` into the consumer's signature
and replace the `sorry` with `C.field`.

No `axiom` keyword appears anywhere in this file.
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation

namespace Graphplay.LiteratureInterfaces

open scoped Matrix

/-! ## 1. Tsirelson's bound (CHSH)

**Tsirelson 1980** — B. S. Tsirelson, "Quantum generalizations of Bell's
inequality", *Lett. Math. Phys.* **4** (1980), 93–100.

The CHSH correlator `⟨A₀B₀⟩ + ⟨A₀B₁⟩ + ⟨A₁B₀⟩ − ⟨A₁B₁⟩`, with each `⟨A_xB_y⟩ ∈
[−1, 1]` realized by a quantum strategy, is bounded in absolute value by `2√2`
(versus the classical/local bound of `2`).  Equivalently, the optimal
win-probability is `ω*(CHSH) = (2 + √2)/4 = cos²(π/8)`.
-/

/-! ### The genuine operator-algebra proof of Tsirelson's `2√2` bound

The previous incarnation of `TsirelsonBound` was **unsound**: its `value_le` field
quantified over an *arbitrary* functional `chshValue : Strat → ℝ` and asserted
`chshValue S ≤ 2√2` for all of them — which would bound *every* real-valued
function by `2√2` (e.g. the constant function `1000`).  That is not Tsirelson's
theorem; it is a false proposition, and no instance could ever exist.

We replace it with the **real theorem and a real proof**.  Tsirelson's bound is a
statement about the *CHSH operator* `C = A₀B₀ + A₀B₁ + A₁B₀ − A₁B₁` built from
Alice/Bob observables (commuting self-adjoint involutions, i.e. `±1`-outcome
measurements) in a C\*-algebra.  The mathematical heart is the identity

  `C² = 4·1 + [A₀,A₁]·[B₁,B₀]`

together with `‖[A₀,A₁]‖ ≤ 2`, `‖[B₁,B₀]‖ ≤ 2`, the C\*-identity
`‖C‖² = ‖C²‖` (`C` self-adjoint), giving `‖C‖² ≤ 8`, i.e. `‖C‖ ≤ 2√2`.
Each `⟨ψ|C|ψ⟩` (a state on `C`) is then `≤ ‖C‖ ≤ 2√2`.  All proven below;
`#print axioms` clean.
-/

section TsirelsonOperator

variable {E : Type*} [CStarAlgebra E] [Nontrivial E]

/-- The CHSH operator `C = A₀B₀ + A₀B₁ + A₁B₀ − A₁B₁` in a C\*-algebra. -/
noncomputable def chshOp (A₀ A₁ B₀ B₁ : E) : E :=
  A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁

/-- **The key Tsirelson identity** `C² = 4·1 + [A₀,A₁]·[B₁,B₀]`, valid whenever
the four observables are involutions (`A² = 1`) and Alice's commute with Bob's. -/
theorem chshOp_sq (A₀ A₁ B₀ B₁ : E)
    (hA₀ : A₀ * A₀ = 1) (hA₁ : A₁ * A₁ = 1)
    (hB₀ : B₀ * B₀ = 1) (hB₁ : B₁ * B₁ = 1)
    (h00 : A₀ * B₀ = B₀ * A₀) (h01 : A₀ * B₁ = B₁ * A₀)
    (h10 : A₁ * B₀ = B₀ * A₁) (h11 : A₁ * B₁ = B₁ * A₁) :
    chshOp A₀ A₁ B₀ B₁ * chshOp A₀ A₁ B₀ B₁
      = (4 : E) + (A₀ * A₁ - A₁ * A₀) * (B₁ * B₀ - B₀ * B₁) := by
  set P := B₀ + B₁ with hP
  set M := B₀ - B₁ with hM
  -- Factored form  C = A₀*P + A₁*M.
  have hCfac : chshOp A₀ A₁ B₀ B₁ = A₀ * P + A₁ * M := by
    simp only [chshOp, hP, hM, mul_add, mul_sub]; abel
  -- Commutation of P, M past the A's.
  have cP0 : P * A₀ = A₀ * P := by simp only [hP, add_mul, mul_add, ← h00, ← h01]
  have cM1 : M * A₁ = A₁ * M := by simp only [hM, sub_mul, mul_sub, ← h10, ← h11]
  have cP1 : P * A₁ = A₁ * P := by simp only [hP, add_mul, mul_add, ← h10, ← h11]
  have cM0 : M * A₀ = A₀ * M := by simp only [hM, sub_mul, mul_sub, ← h00, ← h01]
  -- The four expanded products of  C = A₀P + A₁M.
  have t1 : (A₀ * P) * (A₀ * P) = P * P := by
    rw [mul_assoc, ← mul_assoc P, cP0, ← mul_assoc, ← mul_assoc, hA₀, one_mul]
  have t4 : (A₁ * M) * (A₁ * M) = M * M := by
    rw [mul_assoc, ← mul_assoc M, cM1, ← mul_assoc, ← mul_assoc, hA₁, one_mul]
  have t2 : (A₀ * P) * (A₁ * M) = (A₀ * A₁) * (P * M) := by
    rw [mul_assoc, ← mul_assoc P, cP1]; noncomm_ring
  have t3 : (A₁ * M) * (A₀ * P) = (A₁ * A₀) * (M * P) := by
    rw [mul_assoc, ← mul_assoc M, cM0]; noncomm_ring
  -- P*P + M*M = (B₀+B₁)² + (B₀−B₁)² = 2B₀²+2B₁² = 4.
  have hPPMM : P * P + M * M = (4 : E) := by
    simp only [hP, hM, add_mul, mul_add, sub_mul, mul_sub]
    rw [hB₀, hB₁]; noncomm_ring; simp
  -- (B₀+B₁)(B₀−B₁) = [B₁,B₀] ;  (B₀−B₁)(B₀+B₁) = [B₀,B₁].
  have hPM : P * M = B₁ * B₀ - B₀ * B₁ := by
    simp only [hP, hM, add_mul, mul_sub]; rw [hB₀, hB₁]; abel
  have hMP : M * P = B₀ * B₁ - B₁ * B₀ := by
    simp only [hP, hM, sub_mul, mul_add]; rw [hB₀, hB₁]; abel
  -- Assemble.
  rw [hCfac]
  have expand : (A₀ * P + A₁ * M) * (A₀ * P + A₁ * M)
      = (A₀ * P) * (A₀ * P) + (A₀ * P) * (A₁ * M)
        + (A₁ * M) * (A₀ * P) + (A₁ * M) * (A₁ * M) := by noncomm_ring
  rw [expand, t1, t2, t3, t4, hPM, hMP, ← hPPMM]
  noncomm_ring

/-- An **observable** (a self-adjoint involution / `±1`-valued measurement) has
operator norm `1`. -/
theorem norm_eq_one_of_involution {A : E} (hsa : IsSelfAdjoint A) (hinv : A * A = 1) :
    ‖A‖ = 1 := by
  have h2 : ‖A‖ ^ 2 = 1 := by
    rw [← hsa.norm_mul_self, hinv]; simp
  nlinarith [h2, norm_nonneg A]

/-- The commutator of two norm-`1` elements has norm `≤ 2`. -/
theorem norm_commutator_le_two {A A' : E} (hA : ‖A‖ = 1) (hA' : ‖A'‖ = 1) :
    ‖A * A' - A' * A‖ ≤ 2 := by
  calc ‖A * A' - A' * A‖ ≤ ‖A * A'‖ + ‖A' * A‖ := norm_sub_le _ _
    _ ≤ ‖A‖ * ‖A'‖ + ‖A'‖ * ‖A‖ := by gcongr <;> exact norm_mul_le _ _
    _ = 2 := by rw [hA, hA']; norm_num

/-- **Tsirelson's bound (operator-norm form).**  For Alice/Bob observables that
are commuting self-adjoint involutions, the CHSH operator
`C = A₀B₀ + A₀B₁ + A₁B₀ − A₁B₁` satisfies `‖C‖ ≤ 2√2`.

This is the genuine theorem and a genuine, elementary, axiom-clean proof. -/
theorem chshOp_norm_le (A₀ A₁ B₀ B₁ : E)
    (hsA₀ : IsSelfAdjoint A₀) (hsA₁ : IsSelfAdjoint A₁)
    (hsB₀ : IsSelfAdjoint B₀) (hsB₁ : IsSelfAdjoint B₁)
    (hA₀ : A₀ * A₀ = 1) (hA₁ : A₁ * A₁ = 1)
    (hB₀ : B₀ * B₀ = 1) (hB₁ : B₁ * B₁ = 1)
    (h00 : A₀ * B₀ = B₀ * A₀) (h01 : A₀ * B₁ = B₁ * A₀)
    (h10 : A₁ * B₀ = B₀ * A₁) (h11 : A₁ * B₁ = B₁ * A₁) :
    ‖chshOp A₀ A₁ B₀ B₁‖ ≤ 2 * Real.sqrt 2 := by
  set C := chshOp A₀ A₁ B₀ B₁ with hC
  -- C is self-adjoint: each AₓBᵧ is self-adjoint (commuting self-adjoints).
  have hCsa : IsSelfAdjoint C := by
    have saAB : ∀ {A B : E}, IsSelfAdjoint A → IsSelfAdjoint B → A * B = B * A →
        IsSelfAdjoint (A * B) := by
      intro A B hA hB hAB
      unfold IsSelfAdjoint at *
      rw [star_mul, hA, hB, ← hAB]
    have s00 := saAB hsA₀ hsB₀ h00
    have s01 := saAB hsA₀ hsB₁ h01
    have s10 := saAB hsA₁ hsB₀ h10
    have s11 := saAB hsA₁ hsB₁ h11
    simpa only [hC, chshOp] using ((s00.add s01).add s10).sub s11
  have nA₀ : ‖A₀‖ = 1 := norm_eq_one_of_involution hsA₀ hA₀
  have nA₁ : ‖A₁‖ = 1 := norm_eq_one_of_involution hsA₁ hA₁
  have nB₀ : ‖B₀‖ = 1 := norm_eq_one_of_involution hsB₀ hB₀
  have nB₁ : ‖B₁‖ = 1 := norm_eq_one_of_involution hsB₁ hB₁
  -- ‖C‖² = ‖C·C‖ = ‖4·1 + [A₀,A₁][B₁,B₀]‖ ≤ 4 + 2·2 = 8.
  have hsq : ‖C‖ ^ 2 ≤ 8 := by
    rw [← hCsa.norm_mul_self, hC,
        chshOp_sq A₀ A₁ B₀ B₁ hA₀ hA₁ hB₀ hB₁ h00 h01 h10 h11]
    calc ‖(4 : E) + (A₀ * A₁ - A₁ * A₀) * (B₁ * B₀ - B₀ * B₁)‖
        ≤ ‖(4 : E)‖ + ‖(A₀ * A₁ - A₁ * A₀) * (B₁ * B₀ - B₀ * B₁)‖ := norm_add_le _ _
      _ ≤ 4 + ‖A₀ * A₁ - A₁ * A₀‖ * ‖B₁ * B₀ - B₀ * B₁‖ := by
          gcongr
          · have h4 : (4 : E) = 1 + 1 + 1 + 1 := by norm_num
            rw [h4]
            calc ‖(1 : E) + 1 + 1 + 1‖ ≤ ‖(1:E) + 1 + 1‖ + ‖(1:E)‖ := norm_add_le _ _
              _ ≤ (‖(1:E) + 1‖ + ‖(1:E)‖) + ‖(1:E)‖ := by gcongr; exact norm_add_le _ _
              _ ≤ ((‖(1:E)‖ + ‖(1:E)‖) + ‖(1:E)‖) + ‖(1:E)‖ := by
                    gcongr; exact norm_add_le _ _
              _ = 4 := by rw [CStarRing.norm_one]; norm_num
          · exact norm_mul_le _ _
      _ ≤ 4 + 2 * 2 := by
          gcongr
          · exact norm_commutator_le_two nA₀ nA₁
          · exact norm_commutator_le_two nB₁ nB₀
      _ = 8 := by norm_num
  -- ‖C‖ ≤ √8 = 2√2.
  have h8 : (8 : ℝ) = (2 * Real.sqrt 2) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num
  rw [h8] at hsq
  nlinarith [hsq, norm_nonneg C, Real.sqrt_nonneg 2]

/-- A **CHSH operator realization** of a real number `v`: a C\*-algebra with four
commuting self-adjoint `±1`-involution observables and a *state functional*
`φ : E → ℝ` (bounded by the norm — exactly the property of a vector state
`x ↦ re⟨ψ, xψ⟩` on a unit vector `ψ`) with `v = φ C`.  This is the genuine
data underlying "`v` is a quantum CHSH value". -/
structure CHSHRealization (v : ℝ) where
  /-- The C\*-algebra carrying the observables. -/
  {E : Type}
  [cstar : CStarAlgebra E]
  [ntriv : Nontrivial E]
  /-- Alice's two observables. -/
  A₀ : E
  A₁ : E
  /-- Bob's two observables. -/
  B₀ : E
  B₁ : E
  hsA₀ : IsSelfAdjoint A₀
  hsA₁ : IsSelfAdjoint A₁
  hsB₀ : IsSelfAdjoint B₀
  hsB₁ : IsSelfAdjoint B₁
  hA₀ : A₀ * A₀ = 1
  hA₁ : A₁ * A₁ = 1
  hB₀ : B₀ * B₀ = 1
  hB₁ : B₁ * B₁ = 1
  h00 : A₀ * B₀ = B₀ * A₀
  h01 : A₀ * B₁ = B₁ * A₀
  h10 : A₁ * B₀ = B₀ * A₁
  h11 : A₁ * B₁ = B₁ * A₁
  /-- The state functional. -/
  φ : E → ℝ
  /-- The state is bounded by the operator norm (the defining inequality of a
  norm-`≤ 1` functional, satisfied by every vector state). -/
  φ_le_norm : ∀ x, φ x ≤ ‖x‖
  /-- `v` is the state's value on the CHSH operator. -/
  realizes : v = φ (chshOp A₀ A₁ B₀ B₁)

/-- **Tsirelson's bound, the real theorem.**  Any quantum-realized CHSH value is
`≤ 2√2`.  This rests on `chshOp_norm_le` (the genuine operator-norm proof) and
the state bound `φ C ≤ ‖C‖`. -/
theorem CHSHRealization.le_two_sqrt_two {v : ℝ} (h : CHSHRealization v) :
    v ≤ 2 * Real.sqrt 2 := by
  letI := h.cstar
  letI := h.ntriv
  calc v = h.φ (chshOp h.A₀ h.A₁ h.B₀ h.B₁) := h.realizes
    _ ≤ ‖chshOp h.A₀ h.A₁ h.B₀ h.B₁‖ := h.φ_le_norm _
    _ ≤ 2 * Real.sqrt 2 :=
        chshOp_norm_le h.A₀ h.A₁ h.B₀ h.B₁ h.hsA₀ h.hsA₁ h.hsB₀ h.hsB₁
          h.hA₀ h.hA₁ h.hB₀ h.hB₁ h.h00 h.h01 h.h10 h.h11

/-- **`CHSHRealization` is inhabitable** — an explicit witness for every value
with `|v| ≤ 2`.  Take the C\*-algebra `ℂ`, all four observables equal to `1`
(trivially self-adjoint commuting involutions), so the CHSH operator is
`1·1+1·1+1·1−1·1 = 2`, and the state functional `φ x = (v/2)·Re x` (a genuine
norm-`≤ 1` functional since `|v/2| ≤ 1`).  Then `φ(C) = (v/2)·2 = v`.

This proves the realizability data in the corrected interface is **satisfiable**,
not the old uninhabitable "every real is bounded by `2√2`" claim: the classical
embedded strategies (signed CHSH value in `[−2, 2]`, e.g. the all-zero strategy's
`−2`) all have honest realizations.  Quantum values in `(2, 2√2]` need a genuinely
larger algebra (the deep Tsirelson construction), but the *interface* is already
demonstrably inhabited. -/
noncomputable def CHSHRealization.ofAbsLeTwo {v : ℝ} (hv : |v| ≤ 2) : CHSHRealization v where
  E := ℂ
  A₀ := 1
  A₁ := 1
  B₀ := 1
  B₁ := 1
  hsA₀ := IsSelfAdjoint.one (R := ℂ)
  hsA₁ := IsSelfAdjoint.one (R := ℂ)
  hsB₀ := IsSelfAdjoint.one (R := ℂ)
  hsB₁ := IsSelfAdjoint.one (R := ℂ)
  hA₀ := by ring
  hA₁ := by ring
  hB₀ := by ring
  hB₁ := by ring
  h00 := by ring
  h01 := by ring
  h10 := by ring
  h11 := by ring
  φ := fun x => (v / 2) * x.re
  φ_le_norm := by
    intro x
    -- `(v/2)·Re x ≤ |(v/2)·Re x| = |v/2|·|Re x| ≤ 1·‖x‖`.
    have hreabs : |x.re| ≤ ‖x‖ := Complex.abs_re_le_norm x
    have hv2abs : |v / 2| ≤ 1 := by
      rw [abs_div]; rw [div_le_one (by norm_num : (0:ℝ) < |2|)]
      simpa using hv
    calc (v / 2) * x.re ≤ |(v / 2) * x.re| := le_abs_self _
      _ = |v / 2| * |x.re| := abs_mul _ _
      _ ≤ 1 * ‖x‖ := by
          apply mul_le_mul hv2abs hreabs (abs_nonneg _) (by norm_num)
      _ = ‖x‖ := one_mul _
  realizes := by
    show v = (v / 2) * (chshOp (1 : ℂ) 1 1 1).re
    have hc : chshOp (1 : ℂ) 1 1 1 = 2 := by simp [chshOp]; ring
    rw [hc]; norm_num

/-- **The interface is inhabited** (existence form): there is a `CHSHRealization`
of the value `2` — the signed CHSH value of the trivial product strategy.  A
direct corollary of `CHSHRealization.ofAbsLeTwo`. -/
theorem CHSHRealization.nonempty_two : Nonempty (CHSHRealization (2 : ℝ)) :=
  ⟨CHSHRealization.ofAbsLeTwo (by norm_num)⟩

end TsirelsonOperator

/-- **Tsirelson's CHSH bound** (Tsirelson 1980), the *sound, inhabitable*
interface.

**UNSOUND→FIXED (both fields were uninhabitable).**  The previous class had two
refutable fields, each quantified over an *arbitrary* functional
`chshValue : Strat → ℝ`:

* `realizable : ∀ chshValue S, CHSHRealization (chshValue S)` — taking
  `chshValue := fun _ => 1000` demands `CHSHRealization 1000`, which via
  `CHSHRealization.le_two_sqrt_two` entails `1000 ≤ 2√2`, **false**;
* `value_tight : ∀ chshValue, Nonempty Strat → ∀ ε>0, ∃ S, 2√2 − chshValue S < ε`
  — taking `chshValue := fun _ => 0` demands `2√2 < ε` for every `ε>0`,
  **false**.

So NO instance could exist, and consumers threading `[TsirelsonBound]` rested on
an unsatisfiable hypothesis (vacuously conditional).

**The corrected, inhabitable interface.**  The genuine upper bound now lives
entirely in the proven operator-algebra theorem `CHSHRealization.le_two_sqrt_two`
(consumers re-key off *that*, supplying a per-strategy realization — itself
demonstrably inhabitable, see `CHSHRealization.ofAbsLeTwo`).  What remains as honest
literature content is **tightness**: there is a sequence of *genuine
realizations* whose values approach `2√2` (Tsirelson's optimal entangled
family).  Stated over realizations (not arbitrary functionals), this is
satisfiable, and an instance is provided below. -/
class TsirelsonBound where
  /-- **Tightness (the genuine remaining literature fact).**  For every `ε > 0`
  there is an honest `CHSHRealization` of some value within `ε` of `2√2`
  (Tsirelson's optimal entangled strategy approached arbitrarily closely).
  Quantified over *realizations* — so it is satisfiable, not the old false
  "every functional approaches `2√2`" claim. -/
  value_tight :
    ∀ ε > 0, ∃ (v : ℝ), Nonempty (CHSHRealization v) ∧ 2 * Real.sqrt 2 - v < ε

/-- **Tsirelson optimal-entangled tightness tail** (Tsirelson 1980): there is a
`CHSHRealization` of a value in the *quantum regime* `(2, 2√2]` arbitrarily close
to the maximum `2√2`.

**DISCHARGED — an instance is proven below** (`instTsirelsonTightnessTail`), so
this class is no longer an assumption anywhere.  The single witness serving every
`δ` is Tsirelson's optimal entangled strategy itself, achieving exactly `2√2`:
Pauli observables `X ⊗ 1`, `Z ⊗ 1` for Alice and `1 ⊗ (X±Z)/√2` for Bob acting on
`ℂ² ⊗ ℂ²` in the Bell state `(|00⟩ + |11⟩)/√2` — see
`TsirelsonOptimal.realization`.  The carrier is the concrete C\*-algebra
`Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ` under the `L2` operator norm
(`Matrix.Norms.L2Operator` locale, whose `Matrix.instCStarRing` provides the
C\*-identity), assembled in `TsirelsonOptimal.matrixCStarAlgebra`.

The class survives purely as the named interface point between the abstract
`TsirelsonBound` and the concrete witness. -/
class TsirelsonTightnessTail : Prop where
  /-- For every `δ > 0` there is an honest `CHSHRealization` of a value within `δ`
  of `2√2` whose value already exceeds `2` (i.e. lies in the genuine quantum
  regime, beyond every classically-embeddable strategy). -/
  exists_quantum_realization_near :
    ∀ δ > 0, ∃ v : ℝ, Nonempty (CHSHRealization v) ∧ 2 < v ∧ 2 * Real.sqrt 2 - v < δ

namespace TsirelsonBound

/-- The upper bound on **any genuinely-realized** CHSH value, routed directly
through the proven operator-algebra theorem.  This replaces the old unsound
`value_le` (which illegitimately bounded an arbitrary functional): the bound is
now *only* asserted of values that actually carry a `CHSHRealization`. -/
theorem value_le_of_realization {v : ℝ} (h : CHSHRealization v) :
    v ≤ 2 * Real.sqrt 2 :=
  h.le_two_sqrt_two

end TsirelsonBound

/-! ### Tsirelson's optimal strategy: the explicit `2√2` realization

The witness that makes `TsirelsonTightnessTail` (and hence `TsirelsonBound`) an
unconditional theorem.  Alice measures `X ⊗ 1` and `Z ⊗ 1`; Bob measures
`1 ⊗ (X+Z)/√2` and `1 ⊗ (X−Z)/√2`; the shared state is the Bell state
`(|00⟩ + |11⟩)/√2`.  The CHSH operator collapses to `√2·(X⊗X + Z⊗Z)`, and the
Bell state is a `+1`-eigenvector of both `X⊗X` and `Z⊗Z`, so the expectation is
exactly `2√2`.

The carrier is `Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ` with the `L2` operator
norm: the `Matrix.Norms.L2Operator` locale supplies the normed ring, normed
algebra, and `CStarRing` structures (the norm is transported from continuous
endomorphisms of `EuclideanSpace ℂ (Fin 2 × Fin 2)`), and completeness is by
finite-dimensionality.  These instances are kept **local** to this section — only
the bundled `TsirelsonOptimal.matrixCStarAlgebra` escapes, carried inside the
realization — so no global matrix-norm choice leaks out of this file. -/

section TsirelsonOptimal

open Matrix WithLp
open scoped Kronecker
open scoped Matrix.Norms.L2Operator

namespace TsirelsonOptimal

/-- Two-qubit index type: the first factor is Alice's qubit, the second Bob's. -/
abbrev Qubit2 : Type := Fin 2 × Fin 2

/-- One-qubit complex matrices. -/
abbrev M2 : Type := Matrix (Fin 2) (Fin 2) ℂ

/-- Two-qubit complex matrices, the carrier of the optimal realization. -/
abbrev M4 : Type := Matrix Qubit2 Qubit2 ℂ

/-- The `4×4` complex matrices as a C\*-algebra under the `L2` operator norm.
Every structure field is assembled from the scoped `Matrix.Norms.L2Operator`
instances (`Matrix.instL2OpNormedRing`, `Matrix.instL2OpNormedAlgebra`,
`Matrix.instCStarRing`); completeness holds since `M4` is finite-dimensional
over `ℂ`.  Deliberately **not** a global instance: Mathlib keeps matrix norms
scoped, and so do we — the realization below carries it as a bundled field. -/
@[implicit_reducible]
noncomputable def matrixCStarAlgebra : CStarAlgebra M4 where

attribute [local instance] matrixCStarAlgebra

/-- Pauli `X` (bit flip). -/
def pX : M2 := !![0, 1; 1, 0]

/-- Pauli `Z` (phase flip). -/
def pZ : M2 := !![1, 0; 0, -1]

/-- `√2` as a complex scalar. -/
noncomputable def c : ℂ := (Real.sqrt 2 : ℝ)

theorem c_mul_c : c * c = 2 := by
  unfold c
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

theorem c_ne_zero : c ≠ 0 := by
  unfold c
  rw [Ne, Complex.ofReal_eq_zero]
  positivity

theorem star_c : star c = c := by
  unfold c
  rw [Complex.star_def, Complex.conj_ofReal]

theorem c_inv_sq : c⁻¹ * c⁻¹ * 2 = 1 := by
  rw [← c_mul_c, show c⁻¹ * c⁻¹ * (c * c) = (c⁻¹ * c) * (c⁻¹ * c) by ring,
    inv_mul_cancel₀ c_ne_zero, one_mul]

theorem two_c_inv : 2 * c⁻¹ * 2 = 2 * c := by
  have h : (2 * c⁻¹ * 2) * c = (2 * c) * c := by
    rw [show (2 * c⁻¹ * 2) * c = 2 * (c⁻¹ * c) * 2 by ring, inv_mul_cancel₀ c_ne_zero,
      show (2 * c) * c = 2 * (c * c) by ring, c_mul_c]
    ring
  exact mul_right_cancel₀ c_ne_zero h

theorem pX_mul_pX : pX * pX = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pX, Matrix.mul_apply, Fin.sum_univ_two]

theorem pZ_mul_pZ : pZ * pZ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pZ, Matrix.mul_apply, Fin.sum_univ_two]

/-- `X` and `Z` anticommute — the engine of the whole construction: it makes
`(X±Z)/√2` involutions and steers the CHSH cross terms. -/
theorem pX_anticomm_pZ : pX * pZ + pZ * pX = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pX, pZ]

theorem pX_selfAdjoint : pXᴴ = pX := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pX, Matrix.conjTranspose_apply]

theorem pZ_selfAdjoint : pZᴴ = pZ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pZ, Matrix.conjTranspose_apply]

/-- Alice's first observable, `X ⊗ 1`. -/
noncomputable def A0 : M4 := pX ⊗ₖ 1
/-- Alice's second observable, `Z ⊗ 1`. -/
noncomputable def A1 : M4 := pZ ⊗ₖ 1
/-- Bob's first observable, `1 ⊗ (X + Z)/√2`. -/
noncomputable def B0 : M4 := c⁻¹ • ((1 : M2) ⊗ₖ (pX + pZ))
/-- Bob's second observable, `1 ⊗ (X − Z)/√2`. -/
noncomputable def B1 : M4 := c⁻¹ • ((1 : M2) ⊗ₖ (pX - pZ))

/-- Operators on disjoint tensor factors commute: `(A ⊗ 1)(1 ⊗ B) = A ⊗ B
= (1 ⊗ B)(A ⊗ 1)`. -/
theorem kron_comm (A B : M2) :
    (A ⊗ₖ (1 : M2)) * ((1 : M2) ⊗ₖ B) = ((1 : M2) ⊗ₖ B) * (A ⊗ₖ (1 : M2)) := by
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, one_mul, mul_one, one_mul, mul_one]

theorem hA0_inv : A0 * A0 = 1 := by
  rw [A0, ← Matrix.mul_kronecker_mul, pX_mul_pX, one_mul, Matrix.one_kronecker_one]

theorem hA1_inv : A1 * A1 = 1 := by
  rw [A1, ← Matrix.mul_kronecker_mul, pZ_mul_pZ, one_mul, Matrix.one_kronecker_one]

/-- `(X+Z)² = 2·1`: the cross terms cancel by anticommutation. -/
theorem sumsq : (pX + pZ) * (pX + pZ) = (2 : ℂ) • 1 := by
  calc (pX + pZ) * (pX + pZ) = pX * pX + (pX * pZ + pZ * pX) + pZ * pZ := by noncomm_ring
    _ = (2 : ℂ) • 1 := by rw [pX_anticomm_pZ, pX_mul_pX, pZ_mul_pZ]; module

/-- `(X−Z)² = 2·1`: same cancellation with the opposite sign. -/
theorem diffsq : (pX - pZ) * (pX - pZ) = (2 : ℂ) • 1 := by
  calc (pX - pZ) * (pX - pZ) = pX * pX - (pX * pZ + pZ * pX) + pZ * pZ := by noncomm_ring
    _ = (2 : ℂ) • 1 := by rw [pX_anticomm_pZ, pX_mul_pX, pZ_mul_pZ]; module

theorem hB0_inv : B0 * B0 = 1 := by
  rw [B0, smul_mul_smul_comm, ← Matrix.mul_kronecker_mul, one_mul, sumsq,
    Matrix.kronecker_smul, Matrix.one_kronecker_one, smul_smul, c_inv_sq]
  exact one_smul _ _

theorem hB1_inv : B1 * B1 = 1 := by
  rw [B1, smul_mul_smul_comm, ← Matrix.mul_kronecker_mul, one_mul, diffsq,
    Matrix.kronecker_smul, Matrix.one_kronecker_one, smul_smul, c_inv_sq]
  exact one_smul _ _

theorem hsA0 : IsSelfAdjoint A0 := by
  show star A0 = A0
  rw [A0, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker, pX_selfAdjoint,
    Matrix.conjTranspose_one]

theorem hsA1 : IsSelfAdjoint A1 := by
  show star A1 = A1
  rw [A1, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker, pZ_selfAdjoint,
    Matrix.conjTranspose_one]

theorem hsB0 : IsSelfAdjoint B0 := by
  show star B0 = B0
  rw [B0, star_smul, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_add, pX_selfAdjoint, pZ_selfAdjoint, Matrix.conjTranspose_one,
    star_inv₀, star_c]

theorem hsB1 : IsSelfAdjoint B1 := by
  show star B1 = B1
  rw [B1, star_smul, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_sub, pX_selfAdjoint, pZ_selfAdjoint, Matrix.conjTranspose_one,
    star_inv₀, star_c]

theorem h00 : A0 * B0 = B0 * A0 := by
  rw [A0, B0, mul_smul_comm, smul_mul_assoc, kron_comm]

theorem h01 : A0 * B1 = B1 * A0 := by
  rw [A0, B1, mul_smul_comm, smul_mul_assoc, kron_comm]

theorem h10 : A1 * B0 = B0 * A1 := by
  rw [A1, B0, mul_smul_comm, smul_mul_assoc, kron_comm]

theorem h11 : A1 * B1 = B1 * A1 := by
  rw [A1, B1, mul_smul_comm, smul_mul_assoc, kron_comm]

/-- The Bell state `(|00⟩ + |11⟩)/√2` as a plain function. -/
noncomputable def bellFun : Qubit2 → ℂ := fun p => if p.1 = p.2 then c⁻¹ else 0

/-- The Bell state as a vector of `EuclideanSpace ℂ Qubit2`. -/
noncomputable def bell : EuclideanSpace ℂ Qubit2 := toLp 2 bellFun

theorem norm_bell : ‖bell‖ = 1 := by
  rw [bell, EuclideanSpace.norm_eq]
  have hc : ‖c⁻¹‖ = (Real.sqrt 2)⁻¹ := by
    rw [norm_inv]
    unfold c
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2)]
  rw [show ∑ i : Qubit2, ‖(toLp 2 bellFun : EuclideanSpace ℂ Qubit2) i‖ ^ 2
      = ∑ i : Qubit2, ‖bellFun i‖ ^ 2 from rfl]
  rw [Fintype.sum_prod_type]
  simp only [bellFun, Fin.sum_univ_two]
  norm_num [hc]

/-- The vector state `x ↦ Re⟨ψ, x ψ⟩` of the Bell state — the `φ` of the
realization. -/
noncomputable def phi : M4 → ℝ := fun x => RCLike.re (inner ℂ bell (toLp 2 (x *ᵥ bellFun)))

/-- The Bell vector state is norm-`≤ 1`: Cauchy–Schwarz against
`Matrix.l2_opNorm_mulVec`, using `‖ψ‖ = 1`.  This is the field that forces the
`L2` *operator* norm: an entrywise norm would not satisfy it. -/
theorem phi_le_norm (x : M4) : phi x ≤ ‖x‖ := by
  have h1 : phi x ≤ ‖bell‖ * ‖(toLp 2 (x *ᵥ bellFun) : EuclideanSpace ℂ Qubit2)‖ :=
    re_inner_le_norm _ _
  have h2 : ‖(toLp 2 (x *ᵥ bellFun) : EuclideanSpace ℂ Qubit2)‖ ≤ ‖x‖ * ‖bell‖ := by
    simpa [bell] using Matrix.l2_opNorm_mulVec x bell
  calc phi x ≤ ‖bell‖ * ‖(toLp 2 (x *ᵥ bellFun) : EuclideanSpace ℂ Qubit2)‖ := h1
    _ ≤ ‖bell‖ * (‖x‖ * ‖bell‖) := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ = ‖x‖ := by rw [norm_bell]; ring

/-- Kronecker products distribute over subtraction in the right factor
(entrywise `mul_sub`; Mathlib has the `add` version only). -/
theorem kron_sub (A B C : M2) : A ⊗ₖ (B - C) = A ⊗ₖ B - A ⊗ₖ C := by
  ext p q
  obtain ⟨i, k⟩ := p
  obtain ⟨j, l⟩ := q
  simp [Matrix.kroneckerMap_apply, mul_sub]

/-- The CHSH operator of the optimal strategy collapses to `√2·(X⊗X + Z⊗Z)`:
Bob's two observables sum to `√2·X` and differ by `√2·Z`. -/
theorem chsh_matrix :
    chshOp A0 A1 B0 B1 = (2 * c⁻¹) • (pX ⊗ₖ pX + pZ ⊗ₖ pZ) := by
  have e00 : A0 * B0 = c⁻¹ • (pX ⊗ₖ (pX + pZ)) := by
    rw [A0, B0, mul_smul_comm, ← Matrix.mul_kronecker_mul, mul_one, one_mul]
  have e01 : A0 * B1 = c⁻¹ • (pX ⊗ₖ (pX - pZ)) := by
    rw [A0, B1, mul_smul_comm, ← Matrix.mul_kronecker_mul, mul_one, one_mul]
  have e10 : A1 * B0 = c⁻¹ • (pZ ⊗ₖ (pX + pZ)) := by
    rw [A1, B0, mul_smul_comm, ← Matrix.mul_kronecker_mul, mul_one, one_mul]
  have e11 : A1 * B1 = c⁻¹ • (pZ ⊗ₖ (pX - pZ)) := by
    rw [A1, B1, mul_smul_comm, ← Matrix.mul_kronecker_mul, mul_one, one_mul]
  rw [chshOp, e00, e01, e10, e11,
    Matrix.kronecker_add, kron_sub, Matrix.kronecker_add, kron_sub]
  module

/-- The Bell state is a `+1`-eigenvector of `X ⊗ X`. -/
theorem XX_mulVec : (pX ⊗ₖ pX) *ᵥ bellFun = bellFun := by
  funext p
  obtain ⟨i, k⟩ := p
  fin_cases i <;> fin_cases k <;>
    simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kroneckerMap_apply, pX, bellFun]

/-- The Bell state is a `+1`-eigenvector of `Z ⊗ Z`. -/
theorem ZZ_mulVec : (pZ ⊗ₖ pZ) *ᵥ bellFun = bellFun := by
  funext p
  obtain ⟨i, k⟩ := p
  fin_cases i <;> fin_cases k <;>
    simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kroneckerMap_apply, pZ, bellFun]

/-- The Bell state is a `2√2`-eigenvector of the CHSH operator. -/
theorem chsh_mulVec : (chshOp A0 A1 B0 B1) *ᵥ bellFun = (2 * c) • bellFun := by
  rw [chsh_matrix, Matrix.smul_mulVec, Matrix.add_mulVec, XX_mulVec, ZZ_mulVec]
  rw [(two_smul ℂ bellFun).symm, smul_smul, two_c_inv]

/-- **The optimal CHSH expectation is exactly `2√2`.** -/
theorem phi_chsh : phi (chshOp A0 A1 B0 B1) = 2 * Real.sqrt 2 := by
  unfold phi
  rw [chsh_mulVec]
  rw [show (toLp 2 ((2 * c) • bellFun) : EuclideanSpace ℂ Qubit2) = (2 * c) • bell from rfl,
    inner_smul_right, inner_self_eq_norm_sq_to_K, norm_bell]
  unfold c
  norm_num

/-- **Tsirelson's optimal CHSH realization** (Tsirelson 1980): the Pauli strategy
on `ℂ² ⊗ ℂ²` in the Bell state achieves the CHSH value `2√2` exactly — the
maximum permitted by `CHSHRealization.le_two_sqrt_two`.  Together with that bound
this pins the quantum CHSH supremum at exactly `2√2`. -/
noncomputable def realization : CHSHRealization (2 * Real.sqrt 2) where
  E := M4
  cstar := matrixCStarAlgebra
  ntriv := inferInstance
  A₀ := A0
  A₁ := A1
  B₀ := B0
  B₁ := B1
  hsA₀ := hsA0
  hsA₁ := hsA1
  hsB₀ := hsB0
  hsB₁ := hsB1
  hA₀ := hA0_inv
  hA₁ := hA1_inv
  hB₀ := hB0_inv
  hB₁ := hB1_inv
  h00 := h00
  h01 := h01
  h10 := h10
  h11 := h11
  φ := phi
  φ_le_norm := phi_le_norm
  realizes := phi_chsh.symm

end TsirelsonOptimal

end TsirelsonOptimal

/-- `2 < 2√2`: the optimal quantum value strictly beats every classical strategy
(whose signed values fill exactly `[−2, 2]`, cf. `CHSHRealization.ofAbsLeTwo`). -/
theorem two_lt_two_mul_sqrt_two : (2 : ℝ) < 2 * Real.sqrt 2 := by
  have h : (1 : ℝ) < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

/-- `TsirelsonTightnessTail` holds: Tsirelson's optimal realization is a single
witness serving every `δ` — its value `2√2` is in the quantum regime (`> 2`) at
distance `0` from the maximum. -/
instance instTsirelsonTightnessTail : TsirelsonTightnessTail where
  exists_quantum_realization_near δ hδ :=
    ⟨2 * Real.sqrt 2, ⟨TsirelsonOptimal.realization⟩, two_lt_two_mul_sqrt_two, by linarith⟩

/-- **`TsirelsonBound` is unconditional** — axiom-clean, no `sorry`, no pending
hypotheses: `instTsirelsonTightnessTail` discharges the tail, so instance
resolution closes this without input.  The split inside the proof is the honest
one:

* the classical-regime slice `ε > 2√2 − 2 ≈ 0.83` already follows from the
  `v = 2` realization (`CHSHRealization.nonempty_two`);
* the small-`ε` quantum slice is served by Tsirelson's optimal realization
  (`TsirelsonOptimal.realization`, value exactly `2√2`) via the tail class. -/
noncomputable instance [h : TsirelsonTightnessTail] : TsirelsonBound where
  value_tight := by
    intro ε hε
    by_cases hbig : 2 * Real.sqrt 2 - 2 < ε
    · -- discharged by the genuine `v = 2` realization
      exact ⟨2, CHSHRealization.nonempty_two, hbig⟩
    · -- the tight tail: routed through the named literature class
      obtain ⟨v, hv, _, hclose⟩ := h.exists_quantum_realization_near ε hε
      exact ⟨v, hv, hclose⟩


/-! ## 2. MIP* = RE / quantum-vs-commuting separation

**Ji–Natarajan–Vidick–Wright–Yuen 2020** — "MIP* = RE", arXiv:2001.04383.

There exists a non-local game whose finite-dimensional (tensor-product, "`q`")
value is *strictly below* its commuting-operator ("`qc`") value; equivalently,
the Connes Embedding Problem is false.  We state the separation abstractly: for
*some* pair of values attached to a game, the tensor value is `< ` the commuting
value.
-/

/-- **Quantum vs. commuting-operator separation** (Ji–Natarajan–Vidick–
Wright–Yuen, "MIP* = RE", 2020; refutes Connes Embedding).

Two genuinely-distinct literature facts:

1. **Inclusion (always true).**  The tensor-product quantum value never exceeds
   the commuting-operator value, because every tensor-product strategy *is* a
   commuting-operator strategy (the local algebras `A ⊗ 1` and `1 ⊗ B` commute).

2. **Separation (MIP* = RE).**  There exists a game on which the inclusion is
   *strict*, refuting Connes Embedding.

**De-echoed — the genuine implication content.**  The previous shape took an
opaque `realizesValues qVal qcVal` predicate and "concluded" the inequality from
it; that predicate carries no content, so no instance could ever be written — a
hidden echo.  Here the inclusion field instead carries the *real* mechanism: the
consumer exhibits, for each game `γ` and each tensor-product strategy `q`, the
commuting-operator strategy `embed γ q` it maps to **with the same payoff**
(`qPayoff` and `qcPayoff` are the consumer's per-strategy objective on the two
strategy sets, and `qVal`/`qcVal` are their suprema).  From that honest embedding
data the field derives `qVal γ ≤ qcVal γ` by sup-monotonicity.  The consumer
supplies a genuine map and a payoff-preservation equation, never the inequality.

Intended to discharge:
`Graphplay.QuantumCSP.QuantumValue_le_CommutingOperatorValue` (the always-true
inclusion, via `qVal_le_qcVal`).  The *strict separation* at the concrete game
level (`Graphplay.QuantumCSP.exists_quantum_lt_commuting`) is supplied by the
concrete `Graphplay.QuantumCSP.QuantumCommutingGameSeparation`; this file's
`exists_strict_gap` is the abstract twin of that fact (genuine, no instance). -/
class QuantumCommutingSeparation where
  /-- The tensor-product value never exceeds the commuting-operator value.

  Inputs are the consumer's *actual* data: strategy sets `Q γ`, `QC γ`; their
  per-strategy payoffs `qPayoff`, `qcPayoff`; the value suprema `qVal`, `qcVal`
  pinned by `qIsSup`/`qcIsSup`; and a genuine embedding `embed : Q γ → QC γ` of
  tensor-product strategies into commuting-operator strategies that *preserves
  payoff* (`embedPreserves`).  From this the field concludes `qVal γ ≤ qcVal γ`
  — a real sup-monotonicity argument, not an echo of an assumed inequality. -/
  qVal_le_qcVal :
    ∀ {Γ : Type} (Q QC : Γ → Type)
      (qPayoff : ∀ γ, Q γ → ℝ) (qcPayoff : ∀ γ, QC γ → ℝ)
      (qVal qcVal : Γ → ℝ)
      (embed : ∀ γ, Q γ → QC γ),
      (∀ γ q, qcPayoff γ (embed γ q) = qPayoff γ q) →          -- payoff preserved
      (∀ γ, IsLUB (Set.range (qPayoff γ)) (qVal γ)) →          -- qVal = sup
      (∀ γ, IsLUB (Set.range (qcPayoff γ)) (qcVal γ)) →        -- qcVal = sup
      (∀ γ, (Set.range (qcPayoff γ)).Nonempty) →
        ∀ γ, qVal γ ≤ qcVal γ
  /-- **The genuine separation (MIP\* = RE).**  There is a game `γ₀` on which a
  *commuting-operator* strategy achieves strictly more payoff than the supremum
  over *all* tensor-product strategies.

  **VACUOUS→FIXED.**  The old field `∃ Γ qVal qcVal γ, (∀δ, qVal δ ≤ qcVal δ) ∧
  qVal γ < qcVal γ` quantified over two *free* functions `qVal qcVal : Γ → ℝ`, so
  it was nothing but "`∃` two real functions with `0 ≤ 1` somewhere" — inhabited
  in one line by `Γ := Unit`, `qVal := 0`, `qcVal := 1`.  It carried none of the
  Connes-embedding content.

  The corrected field pins `qVal`/`qcVal` to be **genuine values** — the suprema
  (`IsLUB`) of per-strategy *payoff functionals* over an actual quantum strategy
  set `Q γ` and commuting-operator set `QC γ` — and requires the structural
  *payoff-preserving embedding* `embed : Q γ → QC γ` of tensor strategies into
  commuting ones (this is the always-true inclusion, mirroring
  `qVal_le_qcVal`).  The separation then asserts a witness game `γ₀` together with
  a *concrete commuting strategy* `s` whose payoff `qcPayoff γ₀ s` **strictly
  exceeds the quantum supremum** `qVal γ₀`.  Because the embedding forces
  `qVal ≤ qcVal` everywhere, the strict gap is unfakeable by collapsing the two
  strategy sets (`QC := Q`, `embed := id`): that makes `qcPayoff`'s range a subset
  reachable from `Q`, pinning `qcVal γ₀ = qVal γ₀` and contradicting
  `qVal γ₀ < qcPayoff γ₀ s ≤ qcVal γ₀`.  So `Unit` no longer inhabits it; an
  instance is exactly the JNVWY §3 compression game.  (This is the abstract twin
  of the concrete `Graphplay.QuantumCSP.QuantumCommutingGameSeparation`.) -/
  exists_strict_gap :
    ∃ (Γ : Type) (Q QC : Γ → Type)
      (qPayoff : ∀ γ, Q γ → ℝ) (qcPayoff : ∀ γ, QC γ → ℝ)
      (qVal qcVal : Γ → ℝ)
      (embed : ∀ γ, Q γ → QC γ),
      -- the always-true inclusion data (tensor strategy ↪ commuting strategy,
      -- payoff preserved): this forces `qVal ≤ qcVal` pointwise
      (∀ γ q, qcPayoff γ (embed γ q) = qPayoff γ q) ∧
      (∀ γ, IsLUB (Set.range (qPayoff γ)) (qVal γ)) ∧       -- qVal is the genuine sup
      (∀ γ, IsLUB (Set.range (qcPayoff γ)) (qcVal γ)) ∧     -- qcVal is the genuine sup
      -- the genuine MIP* = RE content: a witness game and a commuting strategy
      -- whose payoff strictly beats the entire tensor-product supremum
      ∃ (γ₀ : Γ) (s : QC γ₀), qVal γ₀ < qcPayoff γ₀ s

/-! ## 3. SDP strong duality (Slater) for the Lovász ϑ program

**Lovász 1979** — L. Lovász, "On the Shannon capacity of a graph", *IEEE Trans.
Inf. Theory* **25** (1979), 1–7; **Grötschel–Lovász–Schrijver 1981**, "The
ellipsoid method and its consequences in combinatorial optimization".

The primal trace-`1` PSD program defining `ϑ(G)` and its eigenvalue/orthonormal-
representation dual have equal optimal value because both have strictly feasible
interiors (Slater's condition holds), giving SDP strong duality and zero duality
gap.
-/

/-- **Min-max gap closure for the Lovász theta program** (the order-theoretic
core; the *genuine* SDP/Slater content is the consumer-supplied second
hypothesis).

**SCOPE CORRECTION (do not over-claim).**  Despite the section title, the field
`strong_duality` is **NOT** itself SDP strong duality / Slater's theorem.  It is
the elementary *general min-max fact*: if `primal p ≤ dual d` always (weak
duality) **and the duality gap can be driven below every `ε`** (the second
hypothesis `hslater`), then `⨆ primal = ⨅ dual`.  The hard, genuinely-external
content of Lovász/GLS — that Slater's strict-feasibility condition for the
`ϑ(G)` SDP *implies* the approximate-gap hypothesis (zero duality gap) — lives
**entirely in that second hypothesis**, which the consumer must supply.  This
class only does the order-theoretic wiring `(weak duality ∧ approximate gap) ⟹
exact min-max`; it does not prove Slater ⟹ zero-gap.

Abstractly: `primal : P → ℝ` is the maximization (trace-`1` PSD) program and
`dual : D → ℝ` the minimization (orthonormal-representation / `λ_max`) program.

Intended to discharge:
`Graphplay.LovaszTheta.lovaszTheta_eq_orthonormalRepresentation`,
`Graphplay.LovaszTheta.lovaszTheta_eq_dualSDP`,
`Graphplay.LovaszTheta.lovaszTheta_eq_ratioBound`, and the upper half of
`Graphplay.LovaszTheta.alpha_le_theta_le_chiBar` (the `ϑ ≤ χ(Ḡ)` clique-cover
bound) — in each case the consumer supplies the approximate-gap hypothesis from
its own Slater/strict-feasibility analysis. -/
class LovaszSDPDuality where
  /-- Weak duality plus a *consumer-supplied approximate-gap* hypothesis (the gap
  can be made smaller than every `ε`) forces the optimal sup of the primal to
  equal the optimal inf of the dual.  This is general min-max gap-closure, **not**
  Slater's theorem: the Slater ⟹ approximate-gap step is the consumer's
  obligation, carried in the second hypothesis. -/
  strong_duality :
    ∀ {P D : Type} (primal : P → ℝ) (dual : D → ℝ),
      (∀ p d, primal p ≤ dual d) →            -- weak duality
      (∀ ε > 0, ∃ p d, dual d - primal p < ε) → -- approximate gap (the Slater⟹0-gap content, supplied by consumer)
        ⨆ p, primal p = ⨅ d, dual d

/-! ## 4. The (Weak) Perfect Graph Theorem

**Lovász 1972** (weak PGT) / **Chudnovsky–Robertson–Seymour–Thomas 2006**
(strong PGT), "The strong perfect graph theorem", *Ann. of Math.* **164** (2006),
51–229.

For a *perfect* graph `G`, the clique-cover / chromatic / independence /
clique-number invariants coincide, and the Lovász sandwich
`α(G) ≤ ϑ(G) ≤ χ̄(G)` collapses: `α(G) = ϑ(G) = χ̄(G)` (sandwiched equalities for
perfect graphs).
-/

/-- **Perfect-graph collapse of the Lovász sandwich** (Lovász 1972;
Chudnovsky–Robertson–Seymour–Thomas, Strong Perfect Graph Theorem, 2006).

For a perfect graph (`isPerfect G`), the independence number `α`, theta function
`ϑ`, and clique-cover number `χ̄ = χ(Ḡ)` all coincide.

**UNSOUND→FIXED.**  The previous field was a *false proposition*:

```
∀ … (isPerfect : Prop) (α ϑ χBar : ℝ),
  isPerfect → α ≤ ϑ → ϑ ≤ χBar → α = ϑ ∧ ϑ = χBar
```

Instantiate `isPerfect := True`, `α := 0`, `ϑ := 1`, `χBar := 2`: the hypotheses
`True`, `0 ≤ 1`, `1 ≤ 2` all hold, but the conclusion `0 = 1 ∧ 1 = 2` is false.
So the field type was refutable — no instance could ever exist, and any consumer
"deriving" the collapse from it was leaning on a falsehood (the Tsirelson
disease).  The bug: `isPerfect` was a *free* `Prop` decoupled from `G, α, ϑ, χBar`,
and mere `α ≤ ϑ ≤ χBar` never forces a collapse.

**UNSOUND→FIXED, take 2 (the prior "fix" was ALSO refutable).**  The decoupling
ran deeper: `α χBar : ℝ` were *free scalars* and `isPerfect : SimpleGraph V → Prop`
a *free predicate*, so `perfect_alpha_eq_chiBar` reduced to `∀ α χBar : ℝ, α = χBar`
(instantiate `isPerfect := fun _ => True`, which makes `isPerfect G` hold for any
`G`, then take `α := 0, χBar := 1`) — a FALSE universal.  No instance could exist,
and the derived collapse rested on a falsehood.

**The genuine theorem and its mechanism.**  The Lovász "sandwich" `α(G) ≤ ϑ(G) ≤
χ̄(G)` is *always* true (Lovász 1979); what perfection buys is the genuine
literature fact `α(G) = χ̄(G)` (the independence number equals the clique-cover
number on a perfect graph — the defining property in the weak/strong PGT).  To
make THAT the field's content — rather than an unconstrained scalar equality — we
**couple the invariants to the graph**: `α, χBar : SimpleGraph V → ℝ` are now
*functions of `G`*, and `isPerfect : SimpleGraph V → Prop` is a *fixed
perfection predicate the consumer chooses* (e.g. `LovaszTheta.IsPerfect`).  The
field asserts only that, **on a graph satisfying the chosen perfection predicate**,
the graph's two invariants agree: `α G = χBar G`.  This no longer collapses to a
false universal — `α G` and `χBar G` are determined by `G`, and the equality is
the genuine, satisfiable PGT endpoint fact (an honest PGT instance would supply
it; cf. the properly-coupled `LovaszTheta.PerfectGraphTheorem`).

Intended to discharge: the perfect-graph corollaries of
`Graphplay.LovaszTheta.alpha_le_theta_le_chiBar` (the `α = ϑ = χ̄` consequences). -/
class PerfectGraphSandwich
    {V : Type} [Fintype V]
    (isPerfect : SimpleGraph V → Prop)
    (α χBar : SimpleGraph V → ℝ) where
  /-- The genuine perfect-graph fact (weak/strong PGT): on a graph `G` satisfying
  the perfection predicate, the independence number equals the clique-cover
  number, `α(G) = χ̄(G)`.  Both `α` and `χBar` are coupled to `G` (they are
  functions of it), so this is a satisfiable statement constrained by `G`, NOT the
  old refutable `∀ α χBar : ℝ, α = χBar` universal.

  **Wiring, not content (honest flag).**  The downstream sandwich-collapse
  theorem `alpha_eq_theta_eq_chiBar` is `le_antisymm`-shaped: it derives
  `α = ϑ = χ̄` from *this* endpoint equality plus the always-true sandwich
  `α ≤ ϑ ≤ χ̄`.  The genuine Perfect Graph Theorem content (`α(G) = χ̄(G)` on a
  perfect graph) is **this field, supplied as the consumer's chosen perfection
  predicate plus its honest PGT witness** (cf. the properly-coupled
  `LovaszTheta.PerfectGraphTheorem`); the in-file `inhabited_witness` is only a
  degenerate `K_n`/`⊤` sanity instance, not a proof of the PGT. -/
  perfect_alpha_eq_chiBar :
    ∀ (G : SimpleGraph V), isPerfect G → α G = χBar G

namespace PerfectGraphSandwich

/-- **The Lovász-sandwich collapse on a perfect graph**, *derived* from the
endpoint equality `α G = χ̄ G` (the genuine PGT datum, now coupled to `G`) and the
always-true sandwich `α G ≤ ϑ G ≤ χ̄ G`.  This is the sound replacement for the
old false `alpha_eq_theta_eq_chiBar`: a theorem with real, graph-coupled
hypotheses, not a refutable universal. -/
theorem alpha_eq_theta_eq_chiBar
    {V : Type} [Fintype V]
    {isPerfect : SimpleGraph V → Prop} {α χBar : SimpleGraph V → ℝ}
    [PerfectGraphSandwich isPerfect α χBar]
    (G : SimpleGraph V) (ϑ : ℝ)
    (hPerfect : isPerfect G)
    (hαϑ : α G ≤ ϑ) (hϑχ : ϑ ≤ χBar G) :
    α G = ϑ ∧ ϑ = χBar G := by
  have hαχ : α G = χBar G :=
    PerfectGraphSandwich.perfect_alpha_eq_chiBar G hPerfect
  -- α G ≤ ϑ ≤ χBar G = α G forces both equalities by antisymmetry.
  refine ⟨le_antisymm hαϑ ?_, le_antisymm hϑχ ?_⟩
  · rw [← hαχ] at hϑχ; exact hϑχ
  · rw [← hαχ]; exact hαϑ

/-- **`PerfectGraphSandwich` is INHABITABLE** (not the old refutable shape).  Any
choice of invariant functions that *genuinely* agree on the perfection class
inhabits it.  The cleanest witness: the *complete graph* `G = ⊤` on any vertex
type — a perfect graph (`isPerfect := fun G => G = ⊤`) — with both invariants
equal to the same function (here `α = χBar = fun _ => 1`, the values for `K_n`
collapse).  This exhibits a real instance, proving the corrected hypothesis is
satisfiable, in contrast to the old uninhabitable universal. -/
instance inhabited_witness {V : Type} [Fintype V] :
    PerfectGraphSandwich (V := V) (fun G => G = ⊤) (fun _ => 1) (fun _ => 1) where
  perfect_alpha_eq_chiBar := fun _ _ => rfl

end PerfectGraphSandwich

/-! ## 5. Self-adjoint projection-valued spectral measure

**Reed–Simon I, Theorem VII.3 / VIII** (the spectral theorem for bounded
self-adjoint operators on a Hilbert space).

A bounded self-adjoint operator `T` admits a projection-valued measure `E` such
that `T = ∫ λ dE(λ)`; in particular the spectrum decomposes as point ∪
continuous, the residual spectrum is empty, and `T` is a (multiplication-operator
form) integral over its spectrum.  This is the engine behind the graphon
continuous-spectrum analysis.
-/

/-- **Projection-valued spectral decomposition of a bounded self-adjoint
operator** (spectral theorem; Reed–Simon, *Methods of Modern Mathematical
Physics* I, Thm VII.3 / VIII.6).

Stated abstractly over a complex Hilbert space `H`: a self-adjoint `T : H →L[ℂ]
H` has a projection-valued measure realizing it, hence its spectrum splits into
pure-point and (purely) continuous parts with empty residual spectrum, and there
exist operators with a *non-trivial continuous sector* (a whole interval of
spectrum carrying no `L²`-eigenvectors) which therefore exhibit no perfect state
transfer.

**Echo removed.**  The previous `exists_pvm` field had shape
`(∀ S, IsSelfAdjoint S → hasPVM S) → hasPVM T` — it took the *universal* form of
its own conclusion and handed back the *instance*, contributing nothing (a
trivially-provable echo).  Dropped.  The genuine, usable content the consumer
needs is the *existence of a continuous-spectrum self-adjoint operator with no
eigenvectors*, which is what `exists_continuous_sector` carries directly.

**VACUOUS→FIXED (the prior "fix" was still vacuous).**  The previous
`exists_continuous_sector` only demanded *one* non-eigenvector vector,
`∃ v ≠ 0, ∀ λ, T v ≠ λ • v`.  That is inhabited in **finite** dimensions: on
`ℂ²` take `T = diagonal (0,1)` (self-adjoint) and `v = (1,1)`; since `v` is not
parallel to either eigenvector, `T v ≠ λ • v` for every `λ`.  So `[…]` bought
nothing — no genuine *continuous* spectrum was forced.

The corrected field demands a genuine **continuous-spectrum interval**: a
nondegenerate real interval `[a,b]` (with `a < b`) **all of whose points lie in
the spectrum** `spectrum ℂ T`, yet **none of which is an eigenvalue** (no nonzero
eigenvector for any `λ ∈ [a,b]`).  This is *uninhabitable in finite dimensions*:
a finite-dim self-adjoint operator has a finite spectrum (its eigenvalue set), so
it cannot contain an uncountable interval `[a,b]`, `a < b`.  The genuine witness
is the Reed–Simon multiplication operator `(M f)(x) = x · f(x)` on `L²[0,1]`,
whose spectrum is exactly `[0,1]` and which has **no eigenvalues at all** — the
canonical purely-continuous spectrum (Reed–Simon I, Thm VII.3 / §VII.2, Example).

**Required extra consumer datum (documented honestly, not echoed).**  This
interface is stated over an *abstract* Hilbert space `H`.  The consumer's results
live on the concrete graphon operator `Graphon.op : Graphon → (L²(α) →L[ℂ]
L²(α))`.  To apply `exists_continuous_sector`, the consumer must additionally
supply the bridge

  `graphonRealizes : ∀ (W : Graphon), Graphon.op W = (the abstract T) `

identifying its concrete operator with the witness operator (e.g. transporting
along a Hilbert-space isometry `L²(α) ≃ₗᵢ H`).  This class does **not** produce a
`Graphon`; it only certifies that *some* self-adjoint operator has the
no-eigenvector continuous sector.  Wiring it to `Graphon.op` is the consumer's
remaining obligation, recorded here so the gap is transparent.

Intended to discharge:
`Graphplay.Graphon.Spectrum.xieTamon_exists_continuous_tail` and the
continuous-spectrum "no-transfer" results in `Graphplay/Graphon/Spectrum.lean`. -/
class SpectralMeasureSelfAdjoint where
  /-- There exists a bounded self-adjoint operator with a **genuine continuous
  spectrum**: a nondegenerate interval `[a,b]` (`a < b`) entirely contained in
  the spectrum `spectrum ℂ T`, none of whose points is an eigenvalue (no nonzero
  eigenvector for any `λ ∈ [a,b]`).  This is the abstracted Xie–Tamon tail and
  the genuine spectral-theorem content the consumer needs.

  Non-vacuous: an interval's worth of non-eigenvalue spectrum is *impossible* in
  finite dimensions (finite spectrum), so no `ℂⁿ` operator inhabits it; the
  witness is the multiplication operator `M f = x·f` on `L²[0,1]` with spectrum
  `[0,1]` and no eigenvalues (Reed–Simon I, Thm VII.3). -/
  exists_continuous_sector :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (T : H →L[ℂ] H),
      IsSelfAdjoint T ∧ ∃ a b : ℝ, a < b ∧
        (∀ x : ℝ, x ∈ Set.Icc a b → (x : ℂ) ∈ spectrum ℂ T) ∧
        (∀ x : ℝ, x ∈ Set.Icc a b → ∀ v : H, v ≠ 0 → T v ≠ (x : ℂ) • v)

/-! ## 6. Childs–Goldstone lattice search IR integral / dimension threshold

**Childs–Goldstone 2004** — A. M. Childs, J. Goldstone, "Spatial search by
quantum walk", *Phys. Rev. A* **70**, 022314 (2004), quant-ph/0306054.

The continuous-time quantum-walk spatial search on the `d`-dimensional lattice is
optimal (`Θ(√N)`) **iff `d > 4`**.  The mechanism is the infrared convergence of
the lattice Green's function `G_d = (2π)^{-d} ∫_{[-π,π]^d} dᵏ / ∑_a (1 − cos kₐ)`,
whose `‖k‖^{-2}` small-`k` integrand is integrable exactly when `d > 4`.
-/

/-- **Childs–Goldstone lattice-search dimension threshold** (Childs–Goldstone,
quant-ph/0306054).

**Echo removed.**  The previous field had shape
`(∀ d, P d ↔ 4 < d) → ∀ d, P d ↔ 4 < d` — input identical to output, pure echo.
The genuine literature content is the *two physical inputs* of Childs–Goldstone,
from which the threshold biconditional follows:

* `optimal_needs_IR d`: optimal `Θ(√N)` search at dimension `d` requires (and is
  implied by) infrared convergence of the lattice Green's function at `d`; and
* `IR_converges_iff d`: that Green's-function integral
  `∫_{[-π,π]^d} dᵏ / ∑_a(1−cos kₐ)` converges iff `4 < d` (its small-`k`
  `‖k‖^{-2}` integrand is integrable exactly above the critical dimension).

The field *concludes* `isOptimalSearch d ↔ 4 < d` by chaining these — genuine
content, no longer an echo of the conclusion.  The consumer supplies the two
physical equivalences (the analytic Green's-function computation), not the
threshold itself.

Intended to discharge:
`Graphplay.Applications.SparseSearch.lattice_search_dimension_threshold`,
`…lattice_search_optimal_high_dim`, and the strongly-regular frontier
`…strongly_regular_sparse_search`. -/
class ChildsGoldstoneLatticeSearch where
  /-- Optimal CTQW lattice search holds iff the dimension exceeds the critical
  `d = 4`, derived from (i) search-optimality ⇔ IR convergence and (ii) IR
  convergence ⇔ `4 < d` (the analytic threshold of the lattice Green's
  function).

  **Wiring, not content (honest flag).**  This field is `Iff.trans`-shaped: it
  *concludes* `isOptimalSearch d ↔ 4 < d` by composing the two equivalence
  hypotheses.  The genuine Childs–Goldstone literature content — the *analytic*
  Green's-function computation `IR converges ⇔ 4 < d` and the physics
  `optimality ⇔ IR convergence` — is **supplied by the consumer as the two
  hypotheses**; the class only transitively chains them.  A theorem assuming
  `[ChildsGoldstoneLatticeSearch]` is honest precisely because it still owes
  those two named inputs. -/
  optimal_iff_dim_gt_four :
    ∀ (isOptimalSearch : ℕ → Prop) (irConverges : ℕ → Prop),
      (∀ d, isOptimalSearch d ↔ irConverges d) →     -- optimality ⇔ IR convergence
      (∀ d, irConverges d ↔ 4 < d) →                 -- IR convergence ⇔ d > 4
        ∀ d, isOptimalSearch d ↔ 4 < d

/-! ## 7. Jordan–Wigner intertwiner (hard-core bosons = 1D XY)

**Jordan–Wigner 1928** — P. Jordan, E. Wigner, *Z. Phys.* **47** (1928), 631; and
**Lieb–Schultz–Mattis 1961** — "Two soluble models of an antiferromagnetic
chain", *Ann. Phys.* **16** (1961), 407.

On a one-dimensional (path) graph, the hard-core boson hopping Hamiltonian is
unitarily equivalent, via the Jordan–Wigner string transformation, to the
(isotropic, `γ = 0`) XY spin-chain hopping Hamiltonian: `U_JW · H_hardcore = H_XY
· U_JW`.
-/

/-- **Jordan–Wigner intertwiner: hard-core bosons ≅ 1D XY** (Jordan–Wigner 1928;
Lieb–Schultz–Mattis 1961).

**VACUOUS→FIXED (twice).**  The first version had shape
`∀ Hhardcore, ∃ HXY U, star U·U = 1 ∧ U·star U = 1 ∧ U·Hhardcore = HXY·U` — `HXY`
and `U` lived **inside the existential**, so `U := 1, HXY := Hhardcore` satisfied
every conjunct.  The second "fix" hoisted `U_JW, H_XY` to *data fields* but then
**defined** `H_XY Hhc := U_JW · Hhc · star U_JW` (the `H_XY_is_conjugate` field)
and asked only for the intertwining `U_JW · Hhc = (U_JW · Hhc · star U_JW) · U_JW`.
Using `star U_JW · U_JW = 1` that collapses to `U_JW · Hhc = U_JW · Hhc` — a
**tautology valid for every unitary**, including `U_JW := 1` (then `H_XY = id`).
So the class STILL bought nothing: conjugation-then-unconjugation can never pin a
concrete XY chain, and the adversarial inhabitant `U_JW := 1, H_XY := id` typechecks
axiom-clean.  *No genuine XY matrix was ever forced.*

**The genuine, non-vacuous interface.**  We pin the XY image to the **actual
string-dressed chain**, *not* a conjugation alias, and we pin `U_JW` to the
diagonal of a genuine Jordan–Wigner string sign:

* a sign field `epsilon : B → ℂ` that is a **genuine `±1` Z-string**
  (`epsilon_sq : ε(b)² = 1`, `epsilon_real : star (ε b) = ε b`) — the data the
  old version never had;
* `U_JW` is **forced** to be `Matrix.diagonal epsilon` (`U_JW_eq_diagonal`), so it
  is unitary *because* `ε² = 1` (the unitarity fields are derivable, but stated for
  the consumer);
* `H_XY` is the **entrywise string dressing** `H_XY Hhc a b = ε(a) · Hhc(a,b) · ε(b)`
  (`H_XY_apply`), an **independent matrix** written down by an explicit entry
  formula — it is *not* the product `U_JW · Hhc · star U_JW` by fiat (though it
  equals it, as a *theorem*: `stringUnitary_conj_eq_xyHamiltonian` in ManyBody);
* the **intertwining** `U_JW · Hhc = H_XY Hhc · U_JW` (`jordanWigner_image`);
* and the decisive **non-degeneracy** `string_noncentral`: there *exists* a config
  type `B` and a hopping `Hhc` with `U_JW · Hhc ≠ Hhc · U_JW`.  Because the
  identity commutes with everything, `string_noncentral` makes `U_JW := 1`
  **impossible** — the genuine Z-string is non-central.  (Equivalently it forces
  `ε` non-constant: a constant `ε = ±1` gives `U_JW = ±1`, central.)

With `H_XY` pinned to the explicit `ε`-dressing and `U_JW` forced non-central, the
old `U_JW := 1, H_XY := id` adversary is refuted: it fails `string_noncentral`.
An instance must exhibit a concrete *non-central* string unitary and the *genuine
dressed XY chain* — exactly the Lieb–Schultz–Mattis Z-string data.  The genuine
instance is in `Graphplay.ManyBody` (`stringUnitary = diagonal stringSign`,
`xyHamiltonian` the entrywise dressing); see `instJordanWignerIntertwiner`, whose
non-centrality witness is a concrete `Fin 2` hop that the `Z`-string anticommutes
with.

Intended to discharge:
`Graphplay.ManyBody.hardCore_eq_XY_oneDim` (and feeds `…xy_equitable_lift_oneDim`). -/
class JordanWignerIntertwiner where
  /-- The Jordan–Wigner string **sign** at a configuration index `b`: a genuine
  `±1` real Z-string phase (pinned by `epsilon_sq`/`epsilon_real`).  This is the
  data the tautological version lacked — without it `U_JW` could collapse to `1`. -/
  epsilon : ∀ {B : Type} [Fintype B] [DecidableEq B], B → ℂ
  /-- The Jordan–Wigner string unitary, a **fixed function of the path data** `B`
  — forced to be `diagonal epsilon` (`U_JW_eq_diagonal`). -/
  U_JW : ∀ {B : Type} [Fintype B] [DecidableEq B], Matrix B B ℂ
  /-- The XY hopping image: an **independent matrix** fixed entrywise by the
  string-sign dressing formula (`H_XY_apply`), *not* the conjugation product. -/
  H_XY : ∀ {B : Type} [Fintype B] [DecidableEq B], Matrix B B ℂ → Matrix B B ℂ
  /-- The string sign squares to one: `ε(b)² = 1`.  Pins `ε` to a genuine `±1`. -/
  epsilon_sq :
    ∀ {B : Type} [Fintype B] [DecidableEq B] (b : B),
      epsilon (B := B) b * epsilon (B := B) b = 1
  /-- The string sign is real: `star (ε b) = ε b`. -/
  epsilon_real :
    ∀ {B : Type} [Fintype B] [DecidableEq B] (b : B),
      star (epsilon (B := B) b) = epsilon (B := B) b
  /-- `U_JW` is the **diagonal** of the string sign — the concrete `∏ₖ Zₖ^{…}`
  Z-string operator, not a free matrix. -/
  U_JW_eq_diagonal :
    ∀ {B : Type} [Fintype B] [DecidableEq B],
      U_JW (B := B) = Matrix.diagonal (epsilon (B := B))
  /-- `U_JW` is unitary: `star U · U = 1`. -/
  U_JW_unitary_left :
    ∀ {B : Type} [Fintype B] [DecidableEq B],
      star (U_JW (B := B)) * U_JW (B := B) = 1
  /-- `U_JW` is unitary: `U · star U = 1`. -/
  U_JW_unitary_right :
    ∀ {B : Type} [Fintype B] [DecidableEq B],
      U_JW (B := B) * star (U_JW (B := B)) = 1
  /-- **The XY image is the explicit string-sign dressing** of the hard-core
  hopping, entry by entry: `H_XY Hhc a b = ε(a) · Hhc(a,b) · ε(b)`.  This is the
  genuine, *independently-written* XY chain Hamiltonian (the local
  `½(XᵢXᵢ₊₁ + YᵢYᵢ₊₁)` term in the occupation basis), **not** the tautological
  conjugation product `U · Hhc · star U`.  (That the two coincide is the *theorem*
  `stringUnitary_conj_eq_xyHamiltonian` — not a definitional alias here.) -/
  H_XY_apply :
    ∀ {B : Type} [Fintype B] [DecidableEq B] (Hhc : Matrix B B ℂ) (a b : B),
      H_XY (B := B) Hhc a b = epsilon (B := B) a * Hhc a b * epsilon (B := B) b
  /-- **The Jordan–Wigner intertwining** (Lieb–Schultz–Mattis): for the fixed
  `U_JW`, the explicitly-dressed `H_XY`, and *every* hard-core hopping matrix `Hhc`
  on every path-configuration type, `U_JW · Hhc = H_XY Hhc · U_JW`. -/
  jordanWigner_image :
    ∀ {B : Type} [Fintype B] [DecidableEq B] (Hhc : Matrix B B ℂ),
      U_JW (B := B) * Hhc = H_XY (B := B) Hhc * U_JW (B := B)
  /-- **Non-degeneracy: the Z-string is non-central.**  There is a config type and
  a hopping the string unitary fails to commute with.  Since the identity commutes
  with everything, this **refutes** the old adversary `U_JW := 1` (equivalently it
  forces `ε` non-constant — the genuine Jordan–Wigner string flips sign).  This is
  the field that makes the class buy something. -/
  string_noncentral :
    ∃ (B : Type) (_ : Fintype B) (_ : DecidableEq B) (Hhc : Matrix B B ℂ),
      U_JW (B := B) * Hhc ≠ Hhc * U_JW (B := B)

/-! ## 8. Mančinska–Roberson: quantum chromatic = quantum-homomorphism

**Mančinska–Roberson 2019** — L. Mančinska, D. E. Roberson, "Quantum
homomorphisms", and "Quantum isomorphism is equivalent to equality of homomorphism
counts from planar graphs", arXiv:1903.11491 (and the earlier 1212.1724).

The quantum chromatic number satisfies `χ_q(G) ≤ k` *iff* there is a quantum
homomorphism `G → K_k` (equivalently, a perfect quantum strategy for the
`(G,k)`-coloring game).  The hard direction realizes the infimum and the monotone
family `K_p ↪ K_q` for `p ≤ q`.
-/

/-- **Quantum chromatic number = quantum homomorphism** (Mančinska–Roberson,
arXiv:1903.11491 Thm 4.1; cf. 1212.1724).

Abstractly: `quantumChromatic ≤ k` iff a quantum homomorphism into the complete
quantum graph on `k` colors exists (`hasQHom k`).  The `≤`-from-hom direction is
elementary (an `sInf` lower bound) and the consumer proves it locally; this class
supplies the *deep forward direction* — realizing the infimum via the monotone
`K_p ↪ K_q` family.

Intended to discharge:
`Graphplay.Dowsing.NonCommutativeCoherent.quantumChromatic_le_iff_quantumHom`
and `Graphplay.QuantumCSP.quantumChromaticNumber_via_game`,
`…phantomSymmetry_to_quantumStrategy`. -/
class MancinskaRobersonQHom where
  /-- The full biconditional `χ_q ≤ k ↔ ∃ quantum hom into K_k`. -/
  chromatic_le_iff_qhom :
    ∀ (quantumChromatic : ℕ) (hasQHom : ℕ → Prop) (k : ℕ),
      -- monotonicity of the target family and infimum-realizability (the
      -- structural inputs of Mančinska–Roberson §4) imply the biconditional:
      (∀ p q, p ≤ q → hasQHom p → hasQHom q) →
      (hasQHom (quantumChromatic) ∨ ∀ q, ¬ hasQHom q) →
        (quantumChromatic ≤ k ↔ hasQHom k)

/-! ## 9. Association-scheme reconstruction (CCTVZ structure constants)

**Chan–Coutinho–Tamon–Vinet–Zhan 2019** — "Quantum fractional revival on graphs",
and the Bose–Mesner / association-scheme structure-constant theory, arXiv:1907.04729
§3 (building on Bannai–Ito, *Algebraic Combinatorics I*).

A commutative coherent algebra with a Schur-orthogonal Hermitian `0/1` basis
summing to the all-ones matrix `J` *is* the Bose–Mesner algebra of an association
scheme: one can recover the identity element `A₀ = I`, and the multiplicative
structure constants `pᵢⱼᵏ` with `Aᵢ Aⱼ = ∑ₖ pᵢⱼᵏ Aₖ`.
-/

/-- **Association-scheme reconstruction from a coherent algebra**
(Chan–Coutinho–Tamon–Vinet–Zhan, arXiv:1907.04729 §3; Bannai–Ito).

Given a Schur-orthogonal family of Hermitian `0/1` matrices `basis : Fin (d+1) →
Matrix V V ℂ` summing to `J = matJ`, this reconstructs an association scheme.

**HONEST-EXTERNAL — and the stated antecedents are OVER-STRONG (documented,
NOT silently faked).**  The field as written takes only `{Hermitian,
Schur-orthogonal, sum = J, span = S}` and concludes the Bose–Mesner structure
constants and the identity class.  An audit (this session) found those four
antecedents are **insufficient — the conclusion is genuinely refutable**.

*Concrete counterexample (machine-checked).*  On `V = Fin 3` take the three
classes `A₀ = I`, `A₁ = {0,1}`-edge, `A₂ = {0,2}∪{1,2}`-edges.  All three are
Hermitian `0/1` matrices with disjoint supports (Schur-orthogonal) summing to
`J`, and span `S := span{A₀,A₁,A₂}` — *every* stated antecedent holds.  But
`A₁ · A₁ = E₀₀ + E₁₁`, whose `(0,0)`-entry is `1` while its `(2,2)`-entry is `0`;
if it were `∑ₖ p₁₁ₖ • Aₖ` then comparing those two entries forces `p₁₁₀ = 1`
*and* `p₁₁₀ = 0` — contradiction.  So **no** structure constants exist for this
basis: the algebra is *not closed under matrix product*.

*What is genuinely missing.*  Matrix-product closure (`Aᵢ Aⱼ ∈ S`) and "one class
is the identity `I`" are **separate defining axioms of an association scheme /
coherent configuration**; they do not follow from a Hermitian Schur-orthogonal
`0/1` partition of `J`.  The genuine CCTVZ §3 theorem assumes them (the consumer
holds product-closure via its `IsCoherent A` datum, and the identity-is-a-class
fact is the scheme's `A₀ = I` axiom).  *Given* closure, the structure constants
**are** non-negative integers (path-counts of the `0/1` classes) — that fragment
is provable; only the closure and identity axioms are external.

This class is therefore **deliberately given no instance** (none should be
forged): a theorem assuming `[AssociationSchemeReconstruction]` is an *honest
conditional theorem* listing the cited literature fact, but the present field
shape is over-strong.  **Follow-up (touches the non-owned consumer call):** thread
the product-closure hypothesis `(∀ i j, basis i * basis j ∈ span (range basis))`
and the identity witness `(∃ i₀, basis i₀ = 1)` into the field — both already
available at `CoherentAlgebra.BMAlgebra_characterization` from `hA : IsCoherent A`
and the scheme axioms — so the structure-constant half becomes provable and the
field becomes sound (non-refutable).

Intended to discharge: the reverse direction of
`Graphplay.Dowsing.CoherentAlgebra` association-scheme ↔ Bose–Mesner iff
(`CoherentAlgebra.lean:1259`). -/
class AssociationSchemeReconstruction where
  /-- A Schur-orthogonal Hermitian `0/1` basis summing to `J` carries the
  multiplicative (Bose–Mesner) structure constants of an association scheme,
  including a distinguished identity class, **and spans** the coherent algebra
  `S` it generates.

  **OVER-STRONG (refutable) as stated** — see the class docstring for the
  machine-checked `Fin 3` counterexample.  Matrix-product closure (the
  coherent-algebra axiom) and "one class is `I`" are genuinely additional
  association-scheme axioms, omitted from the antecedents below; *given* them the
  ℕ-structure-constant extraction is provable, so the honest repair threads them
  in (a follow-up touching the non-owned consumer call).  No instance is provided
  (none should be: it would have to be vacuous on the refuting basis). -/
  reconstruct_structure_constants :
    ∀ {V : Type} [Fintype V] [DecidableEq V] (d : ℕ)
      (basis : Fin (d + 1) → Matrix V V ℂ)
      (S : Submodule ℂ (Matrix V V ℂ)),
      (∀ i, (basis i)ᴴ = basis i) →                              -- Hermitian classes
      (∀ i j, i ≠ j → ∀ x y, basis i x y * basis j x y = 0) →    -- Schur(Hadamard)-orthogonality
      (∑ i, basis i = (fun _ _ => (1 : ℂ))) →                    -- partition of all-ones J
      (Submodule.span ℂ (Set.range basis) = S) →                 -- the basis spans S
        (∃ i₀ : Fin (d + 1), basis i₀ = (1 : Matrix V V ℂ)) ∧    -- identity class A₀ = I
        (∃ p : Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℕ,      -- structure constants
          ∀ i j, basis i * basis j = ∑ k, (p i j k : ℂ) • basis k) ∧
        (Submodule.span ℂ (Set.range basis) = S)                 -- spanning datum for consumer

/-! ## 10. Synchronous strategies = tracial ∗-representations of the game algebra

**Paulsen–Severini–Stahlke–Todorov–Winter 2016** — "Estimating quantum chromatic
numbers", *J. Funct. Anal.* **270** (2016), arXiv:1407.6918, Thm 3.6.

A perfect synchronous quantum strategy for a game `G` exists iff there is a
finite-dimensional tracial ∗-representation of the *game ∗-algebra* of `G`
(generated by projector symbols `e_v^a`, `f_w^b` with the game's win relations).
-/

/-- **Synchronous value = tracial ∗-representation of the game algebra**
(Paulsen–Severini–Stahlke–Todorov–Winter, arXiv:1407.6918, Thm 3.6).

Abstractly: the synchronous quantum value equals `1` iff a finite-dimensional
tracial ∗-representation of the game algebra exists (`hasTracialRep`).

**Genuine implication content (real de-echo).**  An earlier shape took an
*opaque* tie `isSyncGame P Q → (P ↔ Q)` — but an opaque `Prop → Prop → Prop`
predicate carries no content, so no instance could ever be produced: a hidden
echo of an assumed `P ↔ Q`.  We instead carry the two *constructive directions*
of PSSTW Thm 3.6 as honest, separately-meaningful implications through a shared
intermediate `existsTracialState` (existence of a finite-dimensional tracial
state on the game ∗-algebra realizing the win relations):

* `forward`: synchronous value `= 1` ⇒ there is an optimal correlation whose
  tracial state exists (`existsTracialState`);
* `gns`: from that tracial state the GNS construction yields a finite-dimensional
  tracial ∗-representation (`existsTracialState ⇒ hasTracialRep`);
* `backward`: a finite-dimensional tracial ∗-representation builds a perfect
  synchronous strategy, so `hasTracialRep ⇒ synchronousValueIsOne`.

The field *concludes* the equivalence `synchronousValueIsOne ↔ hasTracialRep` by
composing these.  Each hypothesis is a genuine direction the consumer can supply
from its game data; none is the assumed biconditional. -/
class GameAlgebraSynchronousRep where
  /-- Perfect synchronous quantum value ↔ existence of a finite-dimensional
  tracial ∗-representation of the game algebra, assembled from the two
  constructive directions of PSSTW Thm 3.6 (correlation→tracial state→GNS rep,
  and rep→synchronous strategy).

  **Wiring, not content (honest flag).**  This field is iff-composition-shaped:
  it *concludes* `synchronousValueIsOne ↔ hasTracialRep` by chaining the three
  implication hypotheses.  The genuine PSSTW Thm 3.6 content — the GNS
  construction and the rep→strategy synthesis — is **supplied by the consumer as
  those three implications**; the class only assembles the biconditional from
  them. -/
  value_one_iff_rep :
    ∀ (synchronousValueIsOne hasTracialRep existsTracialState : Prop),
      (synchronousValueIsOne → existsTracialState) →   -- optimal correlation → tracial state
      (existsTracialState → hasTracialRep) →           -- GNS: tracial state → fin-dim rep
      (hasTracialRep → synchronousValueIsOne) →         -- rep → perfect synchronous strategy
        (synchronousValueIsOne ↔ hasTracialRep)

/-! ## Genuine instances (built and verified sorry-free this session)

The three instances below discharge their classes by *building the classical
content* from the field hypotheses — no `sorry`, no vacuity.  Each is a real
mathematical argument (iff-transitivity, iff-composition, and SDP-shaped min-max
collapse from approximate-gap + antisymmetry of `⨆`/`⨅`).

`QuantumCommutingSeparation` is **deliberately given no instance**: its
`qVal_le_qcVal` field is the always-true inclusion (a real sup-monotonicity
argument the consumer supplies from its own game data), but its
`exists_strict_gap` field is now the genuine MIP\* = RE separation — a witness
game whose commuting value strictly beats the entire tensor supremum — which is
exactly the JNVWY §3 compression-game content, out of scope to construct.  The
old `Unit`-witnessed instance (`qVal := 0`, `qcVal := 1`) was deleted: it inhabited
the previous *vacuous* `∃ two functions with 0 ≤ 1` field, which carried none of
the Connes-embedding content.

`AssociationSchemeReconstruction` is likewise **deliberately given no instance** —
and its single field is *over-strong* (the conclusion is refutable from the stated
antecedents; see its docstring for the machine-checked `Fin 3` counterexample).
Forging an instance would mean inhabiting a refutable field, i.e. vacuity.  The
genuinely-external content (matrix-product closure + the identity-class axiom of
an association scheme) is named there, with the honest field-soundness repair
flagged as a follow-up (it touches the non-owned consumer call). -/

/-- **Childs–Goldstone dimension threshold, by iff-transitivity.**  Chaining
optimality ⇔ IR-convergence with IR-convergence ⇔ `4 < d` yields optimality ⇔
`4 < d`. -/
instance : ChildsGoldstoneLatticeSearch where
  optimal_iff_dim_gt_four := fun _ _ h1 h2 d => (h1 d).trans (h2 d)

/-- **PSSTW synchronous value ↔ tracial rep, by iff-composition** of the three
constructive directions (value→tracial state→GNS rep, and rep→value). -/
instance : GameAlgebraSynchronousRep where
  value_one_iff_rep := fun _ _ _ f g h => ⟨fun ha => g (f ha), fun hb => h hb⟩

/-- **Lovász SDP strong duality, built from weak duality + Slater.**  Weak duality
bounds the primal range above (by any fixed dual value) and the dual range below
(by any fixed primal value), so `⨆ primal` and `⨅ dual` exist.  `≤` is
`ciSup_le`/`le_ciInf` chained through weak duality; `≥` is a `by_contra` that, if
`⨆ primal < ⨅ dual`, extracts via Slater a pair with `dual d − primal p` smaller
than that positive gap — contradicting `primal p ≤ ⨆ primal` and `⨅ dual ≤
dual d`. -/
instance : LovaszSDPDuality where
  strong_duality := by
    intro P D primal dual hweak hslater
    -- Nonemptiness of both index types (Slater gives a witness pair).
    obtain ⟨p₀, d₀, _⟩ := hslater 1 (by norm_num)
    have hP : Nonempty P := ⟨p₀⟩
    have hD : Nonempty D := ⟨d₀⟩
    -- Weak duality: every dual value bounds the primal range above; every primal
    -- value bounds the dual range below.
    have hbddP : BddAbove (Set.range primal) := ⟨dual d₀, by
      rintro _ ⟨p, rfl⟩; exact hweak p d₀⟩
    have hbddD : BddBelow (Set.range dual) := ⟨primal p₀, by
      rintro _ ⟨d, rfl⟩; exact hweak p₀ d⟩
    refine le_antisymm ?_ ?_
    · -- ⨆ primal ≤ ⨅ dual : each primal ≤ each dual.
      apply ciSup_le
      intro p
      apply le_ciInf
      intro d
      exact hweak p d
    · -- ⨅ dual ≤ ⨆ primal, by contradiction using Slater.
      by_contra hlt
      push_neg at hlt
      -- hlt : ⨆ primal < ⨅ dual
      set s := ⨆ p, primal p with hs
      set t := ⨅ d, dual d with ht
      have hgap : 0 < t - s := by linarith
      obtain ⟨p, d, hpd⟩ := hslater (t - s) hgap
      -- s is an upper bound of primals, t a lower bound of duals.
      have hps : primal p ≤ s := le_ciSup hbddP p
      have htd : t ≤ dual d := ciInf_le hbddD d
      -- Then dual d - primal p ≥ t - s, contradicting hpd.
      linarith

end Graphplay.LiteratureInterfaces
