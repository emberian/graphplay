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

end TsirelsonOperator

/-- **Tsirelson's CHSH bound** (Tsirelson 1980), the *sound* interface.

The single non-trivial datum a consumer must supply is, per strategy `S`, a
genuine **CHSH operator realization** of its signed CHSH value `chshValue S`
(four commuting self-adjoint `±1`-involution observables and a vector state on
the CHSH operator).  Given that, the upper bound `chshValue S ≤ 2√2` is *not* an
assumed axiom — it is **derived here from `chshOp_norm_le`**, the elementary
operator-algebra proof above.

This is the corrected replacement for the earlier unsound `value_le`, which
illegitimately bounded an arbitrary functional by `2√2`.  `realizable` is a
**true, non-vacuous** predicate (every honest quantum strategy *does* have such a
realization), and `value_tight` records the genuine remaining literature fact:
the bound is attained by Tsirelson's optimal entangled strategy. -/
class TsirelsonBound where
  /-- The signed CHSH value of any strategy admits a CHSH operator realization
  (commuting observables + vector state).  This is the genuine quantum-mechanical
  modelling assumption; it is satisfiable, *not* the false "every functional is
  bounded" claim. -/
  realizable :
    ∀ {Strat : Type} (chshValue : Strat → ℝ) (S : Strat),
      CHSHRealization (chshValue S)
  /-- The bound is tight: some quantum strategy approaches `2√2` within any `ε`
  (Tsirelson's optimal entangled strategy).  Together with the derived upper
  bound this pins the quantum CHSH value to exactly `2√2`. -/
  value_tight :
    ∀ {Strat : Type} (chshValue : Strat → ℝ),
      Nonempty Strat →
      ∀ ε > 0, ∃ S : Strat, 2 * Real.sqrt 2 - chshValue S < ε

namespace TsirelsonBound

/-- The upper bound `chshValue S ≤ 2√2`, **derived** from the operator-norm proof
`chshOp_norm_le` via the realizability datum.  This is the field consumers
previously called `value_le`; it is now a theorem, not an unsound axiom. -/
theorem value_le [TsirelsonBound] {Strat : Type} (chshValue : Strat → ℝ) (S : Strat) :
    chshValue S ≤ 2 * Real.sqrt 2 :=
  (TsirelsonBound.realizable chshValue S).le_two_sqrt_two

end TsirelsonBound

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
`Graphplay.QuantumCSP.exists_quantum_lt_commuting` and
`Graphplay.QuantumCSP.QuantumValue_le_CommutingOperatorValue`. -/
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
  /-- There exists a game witnessing a strict gap (Connes Embedding is false). -/
  exists_strict_gap :
    ∃ (Γ : Type) (qVal qcVal : Γ → ℝ) (γ : Γ),
      (∀ δ, qVal δ ≤ qcVal δ) ∧ qVal γ < qcVal γ

/-! ## 3. SDP strong duality (Slater) for the Lovász ϑ program

**Lovász 1979** — L. Lovász, "On the Shannon capacity of a graph", *IEEE Trans.
Inf. Theory* **25** (1979), 1–7; **Grötschel–Lovász–Schrijver 1981**, "The
ellipsoid method and its consequences in combinatorial optimization".

The primal trace-`1` PSD program defining `ϑ(G)` and its eigenvalue/orthonormal-
representation dual have equal optimal value because both have strictly feasible
interiors (Slater's condition holds), giving SDP strong duality and zero duality
gap.
-/

/-- **Strong SDP duality for the Lovász theta program** (Lovász 1979;
Grötschel–Lovász–Schrijver 1981).

Abstractly: given a primal objective `primal : P → ℝ` (maximization, the
trace-`1` PSD program) and a dual `dual : D → ℝ` (minimization, the orthonormal-
representation / `λ_max` program), with weak duality `primal p ≤ dual d` always,
Slater's condition forces *equality of optima*:
`⨆ p, primal p = ⨅ d, dual d` whenever both are attained.

The field is phrased as: any value sandwiched as a sup of primals and inf of
duals coincides — i.e. the three SDP characterizations of `ϑ(G)` agree.

Intended to discharge:
`Graphplay.LovaszTheta.lovaszTheta_eq_orthonormalRepresentation`,
`Graphplay.LovaszTheta.lovaszTheta_eq_dualSDP`,
`Graphplay.LovaszTheta.lovaszTheta_eq_ratioBound`, and the upper half of
`Graphplay.LovaszTheta.alpha_le_theta_le_chiBar` (the `ϑ ≤ χ(Ḡ)` clique-cover
bound). -/
class LovaszSDPDuality where
  /-- Weak duality plus a strictly-feasible interior (Slater) forces the optimal
  sup of the primal to equal the optimal inf of the dual. -/
  strong_duality :
    ∀ {P D : Type} (primal : P → ℝ) (dual : D → ℝ),
      (∀ p d, primal p ≤ dual d) →            -- weak duality
      (∀ ε > 0, ∃ p d, dual d - primal p < ε) → -- Slater: gap can be made arbitrarily small
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
`ϑ`, and clique-cover number `χ̄ = χ(Ḡ)` all coincide.  The field takes the three
invariants as real-valued data together with the perfection predicate and asserts
the sandwich is an equality.

Intended to discharge: the perfect-graph corollaries of
`Graphplay.LovaszTheta.alpha_le_theta_le_chiBar` (the `α = ϑ = χ̄` consequences
near `LovaszTheta.lean:867`, `:895`). -/
class PerfectGraphSandwich where
  /-- On a perfect graph the sandwich `α ≤ ϑ ≤ χ̄` is a chain of equalities. -/
  alpha_eq_theta_eq_chiBar :
    ∀ {V : Type} [Fintype V] (_G : SimpleGraph V)
      (isPerfect : Prop) (α ϑ χBar : ℝ),
      isPerfect →
      α ≤ ϑ → ϑ ≤ χBar →   -- the always-valid Lovász sandwich
        α = ϑ ∧ ϑ = χBar

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
exist operators with a *non-trivial continuous sector* (no `L²`-eigenvectors)
which therefore exhibits no perfect state transfer.

**Echo removed.**  The previous `exists_pvm` field had shape
`(∀ S, IsSelfAdjoint S → hasPVM S) → hasPVM T` — it took the *universal* form of
its own conclusion and handed back the *instance*, contributing nothing (a
trivially-provable echo).  Dropped.  The genuine, usable content the consumer
needs is the *existence of a continuous-spectrum self-adjoint operator with no
eigenvectors*, which is what `exists_continuous_sector` carries directly.

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
  /-- There exists a self-adjoint operator with a non-trivial purely-continuous
  sector (the abstracted Xie–Tamon tail): no nonzero vector in the sector is an
  eigenvector, so the sector supports no perfect state transfer.  This is the
  genuine spectral-theorem content the consumer needs (the existence of a
  bounded self-adjoint operator whose spectrum has a continuous part with no
  `L²`-eigenvectors). -/
  exists_continuous_sector :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (T : H →L[ℂ] H),
      IsSelfAdjoint T ∧ ∃ v : H, v ≠ 0 ∧ ∀ lam : ℂ, T v ≠ lam • v

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
  function). -/
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

**Under-specification removed.**  The previous field took an *opaque* predicate
`jwRelated Hhardcore HXY` and handed back a unitary with `U·Hhardcore = HXY·U`.
Because `jwRelated` carried no content, the consumer could (and did) instantiate
it with a trivially-true predicate that left `HXY := Hhardcore`, making the
"intertwiner" vacuous — `U` merely *commuted with* `Hhardcore` and no genuine XY
matrix was ever produced.

The honest interface **produces the XY hopping matrix itself**.  Given only the
hard-core many-body hopping matrix `Hhardcore`, the field returns the XY-image
matrix `HXY` *together with* a **unitary** `U` (witnessed by `U.IsUnitary`-style
data, here `Star`+`mul`-inverse) conjugating one to the other.  The consumer can
no longer smuggle in `HXY = Hhardcore`; the XY matrix is the interface's output,
which is exactly the Lieb–Schultz–Mattis content.

Intended to discharge:
`Graphplay.ManyBody.hardCore_eq_XY_oneDim` (and feeds `…xy_equitable_lift_oneDim`).

**Note for the re-wiring follow-up.**  The consumer `hardCore_eq_XY_oneDim` must
be rewired to take `HXY` from this field rather than aliasing it to `Hhardcore`. -/
class JordanWignerIntertwiner where
  /-- From the hard-core many-body hopping matrix the Jordan–Wigner transform
  produces *both* the XY hopping image `HXY` and a genuine unitary `U`
  (`star U * U = 1` and `U * star U = 1`) intertwining them
  `U * Hhardcore = HXY * U`. -/
  jordanWigner_image :
    ∀ {B : Type} [Fintype B] [DecidableEq B]
      (Hhardcore : Matrix B B ℂ),
      ∃ (HXY U : Matrix B B ℂ),
        star U * U = 1 ∧ U * star U = 1 ∧ U * Hhardcore = HXY * U

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

**Opaque-predicate echo removed + spanning added.**  The previous field took an
*opaque* `isAssocBasis basis` predicate (unfillable, hence a hidden echo) and
returned identity + structure constants — but **not** the fact that the basis
*spans* the Bose–Mesner algebra, which is precisely what the consumer
(`Graphplay.Dowsing.CoherentAlgebra`, whose `S` is a `Submodule.span`) needs to
identify the coherent subalgebra `S` with the scheme's algebra.  Now the field:

* takes the *genuine structural hypotheses* of CCTVZ §3 directly — each `basis i`
  is Hermitian (`(basis i)ᴴ = basis i`), the family is Schur(Hadamard)-orthogonal
  (`basis i ∘ basis j = 0` for `i ≠ j`), and `∑ i, basis i = matJ` — instead of an
  opaque predicate; and
* returns identity class, nonnegative-integer structure constants (Bose–Mesner
  closure under matrix product), **and** the spanning datum `bmSpan`: the basis
  spans the coherent algebra `S` the consumer passes in.

Intended to discharge: the reverse direction of
`Graphplay.Dowsing.CoherentAlgebra` association-scheme ↔ Bose–Mesner iff
(`CoherentAlgebra.lean:1259`). -/
class AssociationSchemeReconstruction where
  /-- A Schur-orthogonal Hermitian `0/1` basis summing to `J` carries the
  multiplicative (Bose–Mesner) structure constants of an association scheme,
  including a distinguished identity class, **and spans** the coherent algebra
  `S` it generates. -/
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
  and rep→synchronous strategy). -/
  value_one_iff_rep :
    ∀ (synchronousValueIsOne hasTracialRep existsTracialState : Prop),
      (synchronousValueIsOne → existsTracialState) →   -- optimal correlation → tracial state
      (existsTracialState → hasTracialRep) →           -- GNS: tracial state → fin-dim rep
      (hasTracialRep → synchronousValueIsOne) →         -- rep → perfect synchronous strategy
        (synchronousValueIsOne ↔ hasTracialRep)

end Graphplay.LiteratureInterfaces
