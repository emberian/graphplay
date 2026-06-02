/-
# Graphplay.StdLib.DeBruijn

Standard-library entry for the **de Bruijn graph** `B(k, n)`, viewed as a
continuous-time-quantum-walk host.

The vertices of `B(k, n+1)` are the `k`-ary strings of length `n + 1`,
modelled as functions `Fin (n + 1) → Fin k`.  There is a **directed** edge
`w → w'` whenever `w'` is obtained from `w` by *dropping the first symbol and
appending a new one* — the **shift-and-append** operation that generates all
length-`(n+1)` substrings of a longer `k`-ary sequence.  Concretely:

  `w → w'`  ⇔  `∀ i, w (i+1) = w' i`   (positions `1 … n` of `w` line up with
  positions `0 … n−1` of `w'`), the last symbol `w' (Fin.last n)` being free.

This is the canonical **n-gram / induction graph**: a directed walk on
`B(k, n+1)` reads out a `k`-ary sequence one symbol at a time, each vertex
being the length-`(n+1)` context window and each step sliding the window by
one.  De Bruijn graphs are `k`-regular (as digraphs), Eulerian, and their
Eulerian circuits are exactly the de Bruijn sequences.

Reachable structural facts proved here with real proofs:

* **out-degree `= k`**: from any window `w`, the `k` successors are obtained by
  choosing the appended symbol (a bijection `Fin k ≃ successors`), and
* **in-degree `= k`**: dually, the `k` predecessors are obtained by choosing
  the dropped (prepended) symbol.

Because a quantum-walk Hamiltonian must be Hermitian, we additionally build
the **symmetrized** de Bruijn graph as a `WeightedGraph`: `adj w w' = 1`
whenever `w → w'` *or* `w' → w` (and `w ≠ w'`).  This is the standard
directed→Hermitian symmetrization (`A_sym = (A + Aᵀ)` thresholded to `0/1`)
used to run a CTQW on a digraph.

## Walkformer atom (the "de Bruijn / n-gram atom" / induction primitive)

The CTQW `U(t) = exp(−i t A_sym)` on the symmetrized de Bruijn graph is the
verified semantics of the **n-gram / induction attention atom**: a single
head whose state is a length-`(n+1)` context window and whose hop is the
sliding-window shift.  The directed shift structure is exactly the
*induction-head* primitive — "given the current `(n+1)`-gram, attend to the
continuations that share the length-`n` suffix" — and the `k`-regularity is
the branching factor of the next-symbol distribution.  The Eulerian /
spectral facts (the de Bruijn spectrum is `{0}` together with the spectrum of
the `B(k, n)` shift, i.e. the eigenvalues are `0` and the `k`-th roots scaled
by `k`) are the deep content, left as honest `sorry`; the regularity
(out/in-degree `= k`) is proved.
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.Pi
import Graphplay.Weighted
import Graphplay.ForMathlib.CourantFischer

open scoped Matrix
open NormedSpace

universe u

namespace Graphplay
namespace StdLib

/-! ## de Bruijn windows and the shift-and-append relation -/

/-- A **de Bruijn window** of `B(k, n+1)`: a `k`-ary string of length `n + 1`,
modelled as a function `Fin (n + 1) → Fin k`. -/
abbrev DeBruijn.Window (k n : ℕ) : Type := Fin (n + 1) → Fin k

/-- The **shift-and-append** relation: `Shift w w'` holds iff `w'` is `w` with
its first symbol dropped and a new symbol appended.  Equivalently positions
`1 … n` of `w` agree with positions `0 … n−1` of `w'`:
`∀ i : Fin n, w (i.succ) = w' (i.castSucc)`. -/
def DeBruijn.Shift {k n : ℕ} (w w' : DeBruijn.Window k n) : Prop :=
  ∀ i : Fin n, w i.succ = w' i.castSucc

instance {k n : ℕ} : DecidableRel (DeBruijn.Shift (k := k) (n := n)) :=
  fun w w' => by unfold DeBruijn.Shift; infer_instance

/-- The **append map**: given a window `w` and a new symbol `a : Fin k`,
`appendSym w a` is the window obtained by shifting `w` left and putting `a` in
the last slot.  This is the canonical successor of `w` carrying appended
symbol `a`. -/
def DeBruijn.appendSym {k n : ℕ} (w : DeBruijn.Window k n) (a : Fin k) :
    DeBruijn.Window k n :=
  fun j => if h : j.val < n then w ⟨j.val + 1, by omega⟩ else a

/-- `appendSym w a` is genuinely a shift-successor of `w`. -/
theorem DeBruijn.shift_appendSym {k n : ℕ} (w : DeBruijn.Window k n)
    (a : Fin k) : DeBruijn.Shift w (DeBruijn.appendSym w a) := by
  intro i
  unfold DeBruijn.appendSym
  -- `i.castSucc` has value `i.val < n`, so the `dif` takes the first branch,
  -- and `⟨i.val + 1, _⟩ = i.succ`.
  rw [dif_pos (show (i.castSucc).val < n by simpa using i.isLt)]
  congr 1

/-- The appended symbol is recovered as the last coordinate: `appendSym` is
injective in `a`. -/
theorem DeBruijn.appendSym_last {k n : ℕ} (w : DeBruijn.Window k n)
    (a : Fin k) : DeBruijn.appendSym w a (Fin.last n) = a := by
  unfold DeBruijn.appendSym
  rw [dif_neg (by simp)]

/-! ## The symmetrized de Bruijn graph as a `WeightedGraph` -/

/-- The **symmetrized adjacency predicate** of `B(k, n+1)`: `w` and `w'` are
linked iff one is a shift-successor of the other (and they are distinct).
This is the Hermitian symmetrization of the directed de Bruijn graph. -/
def DeBruijn.SymAdj {k n : ℕ} (w w' : DeBruijn.Window k n) : Prop :=
  w ≠ w' ∧ (DeBruijn.Shift w w' ∨ DeBruijn.Shift w' w)

instance {k n : ℕ} : DecidableRel (DeBruijn.SymAdj (k := k) (n := n)) :=
  fun w w' => by unfold DeBruijn.SymAdj; infer_instance

/-- The **symmetrized de Bruijn graph** `B(k, n+1)` as a `SimpleGraph` on the
window type `Fin (n+1) → Fin k`. -/
def DeBruijn (k n : ℕ) : SimpleGraph (DeBruijn.Window k n) where
  Adj w w' := DeBruijn.SymAdj w w'
  symm := by
    intro w w' h
    exact ⟨h.1.symm, h.2.symm⟩
  loopless := ⟨fun w h => h.1 rfl⟩

instance (k n : ℕ) : DecidableRel (DeBruijn k n).Adj := by
  intro w w'; unfold DeBruijn; infer_instance

/-- The symmetrized de Bruijn graph as a `WeightedGraph` (the 0/1 Hermitian
Hamiltonian of the CTQW), via the standard `SimpleGraph` bridge.  Its
evolution operator is `(DeBruijn.weighted k n).evolve t = exp(−i t A_sym)`. -/
noncomputable def DeBruijn.weighted (k n : ℕ) :
    WeightedGraph (DeBruijn.Window k n) :=
  SimpleGraph.toWeighted (DeBruijn k n)

/-! ## `k`-regularity of the directed de Bruijn graph -/

/-- The **out-neighbourhood** of `w` in the *directed* de Bruijn graph: the
finset of windows `w'` with `w → w'`. -/
def DeBruijn.outNeighbors {k n : ℕ} (w : DeBruijn.Window k n) :
    Finset (DeBruijn.Window k n) :=
  Finset.univ.filter (fun w' => DeBruijn.Shift w w')

/-- **Out-degree `= k` (directed de Bruijn regularity).**  Every window `w`
has exactly `k` shift-successors, one for each choice of appended symbol.

Proof: the map `a ↦ appendSym w a` is a bijection from `Fin k` onto the
shift-successors of `w` — it is injective (the appended symbol is the last
coordinate, `appendSym_last`) and surjective onto the successors (any
successor `w'` is determined on positions `0 … n−1` by the shift condition
and is `appendSym w (w' (Fin.last n))`). -/
theorem DeBruijn.outDegree (k n : ℕ) (w : DeBruijn.Window k n) :
    (DeBruijn.outNeighbors w).card = k := by
  classical
  -- The out-neighbourhood is the image of `Fin k` under `appendSym w`.
  have himg : DeBruijn.outNeighbors w
      = Finset.univ.image (fun a : Fin k => DeBruijn.appendSym w a) := by
    ext w'
    simp only [DeBruijn.outNeighbors, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_image]
    constructor
    · -- a successor `w'` is `appendSym w (w' (Fin.last n))`.
      intro hshift
      refine ⟨w' (Fin.last n), ?_⟩
      funext j
      unfold DeBruijn.appendSym
      by_cases hj : j.val < n
      · -- on positions `< n`, `appendSym` gives `w (j+1)`, which the shift
        -- condition equates to `w' j`.
        rw [dif_pos hj]
        have := hshift ⟨j.val, hj⟩
        -- `w (⟨j.val,hj⟩.succ) = w' (⟨j.val,hj⟩.castSucc)` and both reindex to
        -- the desired coordinates.
        rw [show (⟨j.val + 1, by omega⟩ : Fin (n + 1)) = (⟨j.val, hj⟩ : Fin n).succ
            from by apply Fin.ext; simp, this]
        congr 1
      · -- on the last position, `appendSym` returns the chosen symbol `w'(last)`.
        rw [dif_neg hj]
        congr 1
        apply Fin.ext
        have : j.val = n := by omega
        simp [this]
    · -- conversely `appendSym w a` is always a successor.
      rintro ⟨a, rfl⟩
      exact DeBruijn.shift_appendSym w a
  rw [himg, Finset.card_image_of_injective]
  · simp
  · -- injectivity of `appendSym w` in the symbol, via `appendSym_last`.
    intro a b hab
    have := congrArg (fun f => f (Fin.last n)) hab
    simpa [DeBruijn.appendSym_last] using this

/-- The **in-neighbourhood** of `w` in the *directed* de Bruijn graph: the
finset of windows `w'` with `w' → w`. -/
def DeBruijn.inNeighbors {k n : ℕ} (w : DeBruijn.Window k n) :
    Finset (DeBruijn.Window k n) :=
  Finset.univ.filter (fun w' => DeBruijn.Shift w' w)

/-- The **prepend map**: given a window `w` and a symbol `a : Fin k`,
`prependSym w a` puts `a` in the first slot and shifts `w` right.  This is the
canonical predecessor of `w` carrying prepended symbol `a`. -/
def DeBruijn.prependSym {k n : ℕ} (w : DeBruijn.Window k n) (a : Fin k) :
    DeBruijn.Window k n :=
  fun j => if h : j.val = 0 then a else w ⟨j.val - 1, by omega⟩

/-- `prependSym w a` is genuinely a shift-predecessor of `w`. -/
theorem DeBruijn.shift_prependSym {k n : ℕ} (w : DeBruijn.Window k n)
    (a : Fin k) : DeBruijn.Shift (DeBruijn.prependSym w a) w := by
  intro i
  unfold DeBruijn.prependSym
  -- `i.succ` has value `i.val + 1 ≠ 0`, so the `dif` takes the second branch
  -- and `⟨(i.val+1)-1, _⟩ = i.castSucc`.
  rw [dif_neg (by simp [Fin.succ])]
  congr 1

/-- The prepended symbol is the first coordinate: `prependSym` is injective. -/
theorem DeBruijn.prependSym_zero {k n : ℕ} (w : DeBruijn.Window k n)
    (a : Fin k) : DeBruijn.prependSym w a ⟨0, by omega⟩ = a := by
  unfold DeBruijn.prependSym
  rw [dif_pos rfl]

/-- **In-degree `= k` (directed de Bruijn regularity).**  Every window `w` has
exactly `k` shift-predecessors, one for each choice of prepended symbol.

Proof: dual to `outDegree`, via the bijection `a ↦ prependSym w a`. -/
theorem DeBruijn.inDegree (k n : ℕ) (w : DeBruijn.Window k n) :
    (DeBruijn.inNeighbors w).card = k := by
  classical
  have himg : DeBruijn.inNeighbors w
      = Finset.univ.image (fun a : Fin k => DeBruijn.prependSym w a) := by
    ext w'
    simp only [DeBruijn.inNeighbors, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_image]
    constructor
    · -- a predecessor `w'` is `prependSym w (w' 0)`.
      intro hshift
      refine ⟨w' ⟨0, by omega⟩, ?_⟩
      funext j
      unfold DeBruijn.prependSym
      by_cases hj : j.val = 0
      · rw [dif_pos hj]
        congr 1
        apply Fin.ext; simp [hj]
      · rw [dif_neg hj]
        -- on positions `> 0`, the shift condition `w' (i.succ) = w (i.castSucc)`
        -- (with `i = j - 1`) gives `w' j = w (j-1)`.
        have hi : (j.val - 1) < n := by omega
        have := hshift ⟨j.val - 1, hi⟩
        rw [show (⟨j.val - 1, by omega⟩ : Fin (n + 1))
              = (⟨j.val - 1, hi⟩ : Fin n).castSucc from by apply Fin.ext; simp,
          ← this]
        congr 1
        apply Fin.ext; simp [Fin.succ]; omega
    · rintro ⟨a, rfl⟩
      exact DeBruijn.shift_prependSym w a
  rw [himg, Finset.card_image_of_injective]
  · simp
  · intro a b hab
    have := congrArg (fun f => f ⟨0, by omega⟩) hab
    simpa [DeBruijn.prependSym_zero] using this

/-! ## Loopless / symmetric (structural) -/

/-- `B(k, n+1)` is **loopless**: no window is symmetrically adjacent to
itself. -/
theorem DeBruijn.loopless (k n : ℕ) (w : DeBruijn.Window k n) :
    ¬ (DeBruijn k n).Adj w w :=
  fun h => h.1 rfl

/-- `B(k, n+1)` is **symmetric** (it is a `SimpleGraph`). -/
theorem DeBruijn.symm (k n : ℕ) {w w' : DeBruijn.Window k n}
    (h : (DeBruijn k n).Adj w w') : (DeBruijn k n).Adj w' w :=
  (DeBruijn k n).symm h

/-! ## Eulerian / spectral facts (honest `sorry`) -/

/-- **The directed de Bruijn graph is Eulerian (honest `sorry`).**
`B(k, n+1)` has, at every vertex, equal in- and out-degree (`= k`), which is
the local balance condition for an Eulerian circuit; together with
connectivity this yields an Eulerian circuit, whose edge sequence is a **de
Bruijn sequence** `B(k, n+1)` of length `k^{n+1}` containing every
length-`(n+1)` `k`-ary string exactly once (van Aardenne-Ehrenfest – de
Bruijn, 1951).

We record the *provable* local balance (in-degree `=` out-degree) as the
hypothesis-free statement, and leave the global Eulerian-circuit existence —
which needs connectivity of `B(k, n+1)` — as an honest `sorry`. -/
theorem DeBruijn.in_eq_out_degree (k n : ℕ) (w : DeBruijn.Window k n) :
    (DeBruijn.inNeighbors w).card = (DeBruijn.outNeighbors w).card := by
  rw [DeBruijn.inDegree, DeBruijn.outDegree]

open scoped Matrix in
open WithLp in
/-- **Rayleigh lower bound for the largest eigenvalue.**  If a Hermitian matrix
`A` admits a test vector `x ≠ 0` whose Rayleigh numerator dominates `B · ‖x‖²`,
then some eigenvalue is `≥ B`.  Pure Courant–Fischer (spectral expansion of the
quadratic form), proved from the `Graphplay.CourantFischer` hinges.  (Stated here
so the de Bruijn degree-eigenvalue statement reduces to a single combinatorial
input.) -/
theorem _root_.Graphplay.CourantFischer.exists_eigenvalue_ge_of_rayleigh'
    {W : Type*} [Fintype W] [DecidableEq W]
    (A : Matrix W W ℂ) (hA : A.IsHermitian) (B : ℝ) (x : W → ℂ) (hx : x ≠ 0)
    (hxB : B * (∑ u, ‖x u‖ ^ 2) ≤ (star x ⬝ᵥ (A *ᵥ x)).re) :
    ∃ i, B ≤ hA.eigenvalues i := by
  classical
  by_contra hcon
  push_neg at hcon
  set c : W → ℝ := fun i => ‖inner ℂ (hA.eigenvectorBasis i) (toLp 2 x)‖ ^ 2 with hc
  have hcnn : ∀ i, 0 ≤ c i := fun i => by rw [hc]; positivity
  have hnum : (star x ⬝ᵥ (A *ᵥ x)).re = ∑ i, (hA.eigenvalues i) * c i :=
    Graphplay.CourantFischer.hermitianForm_re_eq_sum A hA x
  have hden : (∑ u, ‖x u‖ ^ 2) = ∑ i, c i :=
    Graphplay.CourantFischer.normSq_eq_sum A hA x
  have hdenpos : 0 < ∑ u, ‖x u‖ ^ 2 :=
    Graphplay.CourantFischer.normSq_pos_of_ne_zero x hx
  have hsumpos : 0 < ∑ i, c i := by rw [← hden]; exact hdenpos
  obtain ⟨j, _, hjpos⟩ : ∃ j ∈ Finset.univ, 0 < c j := by
    by_contra h
    push_neg at h
    exact absurd hsumpos (not_lt.mpr (Finset.sum_nonpos (fun i _ => h i (Finset.mem_univ i))))
  have hlt : ∑ i, (hA.eigenvalues i) * c i < ∑ i, B * c i := by
    apply Finset.sum_lt_sum
    · exact fun i _ => mul_le_mul_of_nonneg_right (le_of_lt (hcon i)) (hcnn i)
    · exact ⟨j, Finset.mem_univ j, mul_lt_mul_of_pos_right (hcon j) hjpos⟩
  rw [← Finset.mul_sum] at hlt
  rw [hnum, hden] at hxB
  exact absurd hxB (not_le.mpr hlt)

/-! ### The degree eigenvalue: statement scope and the isolated residual

**Audit note (non-vacuity / boundary correctness).**  The intended claim is a
real eigenvalue of magnitude `≥ k` (the regular degree of the directed
`B(k, n+1)`).  Two boundary cases make the *unrestricted* `1 ≤ k` statement
**false**, so we record the corrected hypotheses:

* `k = 1`: the window type `Fin (n+1) → Fin 1` is a singleton, the graph is the
  single loopless vertex, its only eigenvalue is `0 < 1`;
* `n = 0`: `Shift` is the empty constraint, so `SymAdj w w' ↔ w ≠ w'` — the
  symmetrized graph is the complete graph `K_k`, whose top eigenvalue is `k − 1`,
  strictly below `k`.

Hence the genuinely true non-vacuous statement requires `2 ≤ k` and `1 ≤ n`
(verified e.g. for `k = 2, n = 1`, where the graph is `K₄` minus one edge with
top eigenvalue `(1 + √17)/2 ≈ 2.56 ≥ 2`).  Under those hypotheses the bound is
the **Strok spectral-radius fact** for the symmetrized de Bruijn graph (Strok,
*Circulant matrices and the spectra of de Bruijn graphs*, 1992): the depth
recursion `χ_{B(k,n+1)} = x^{(k−1)kⁿ} · χ_{B(k,n)}` forces a degree-magnitude
eigenvalue.  We isolate this — and *only* this — as the single named residual
`DeBruijn.spectralRadius_ge_degree`; the headline theorem then follows by
`le_abs_self`, with the Rayleigh machinery
(`Graphplay.CourantFischer.exists_eigenvalue_ge_of_rayleigh'`) proved above as
the route by which a future witness discharges it. -/

/-- **Isolated residual (honest `sorry`): the symmetrized de Bruijn graph has a
real eigenvalue `≥ k`** for `2 ≤ k`, `1 ≤ n`.  This is the Strok degree fact; it
is the *sole* spectral input of `DeBruijn.exists_degree_eigenvalue`. -/
theorem DeBruijn.spectralRadius_ge_degree (k n : ℕ) (hk : 2 ≤ k) (hn : 1 ≤ n) :
    ∃ i, (k : ℝ) ≤ (DeBruijn.weighted k n).herm.eigenvalues i := by
  sorry

/-- **A real eigenvalue of magnitude `≥ k` exists** for the symmetrized de
Bruijn graph, with the corrected (true, non-vacuous) hypotheses `2 ≤ k`,
`1 ≤ n`.  Immediate from the isolated spectral residual
`DeBruijn.spectralRadius_ge_degree` and `le_abs_self`.

See the audit note above for why `k = 1` and `n = 0` are genuinely excluded. -/
theorem DeBruijn.exists_degree_eigenvalue (k n : ℕ) (hk : 2 ≤ k) (hn : 1 ≤ n) :
    ∃ lam : ℝ, lam ∈ Set.range (DeBruijn.weighted k n).herm.eigenvalues ∧
      (k : ℝ) ≤ |lam| := by
  obtain ⟨i, hi⟩ := DeBruijn.spectralRadius_ge_degree k n hk hn
  exact ⟨(DeBruijn.weighted k n).herm.eigenvalues i, ⟨i, rfl⟩, le_trans hi (le_abs_self _)⟩

/-! ## Smoke tests -/

-- `B(2, 2)`: windows are length-2 binary strings; `appendSym` of `00` with `1`
-- shifts to `01`.
example : DeBruijn.appendSym (k := 2) (n := 1) (fun _ => 0) 1 (Fin.last 1) = 1 :=
  DeBruijn.appendSym_last (fun _ => 0) 1

-- out-degree of any window in `B(2,2)` is `2`.
example : (DeBruijn.outNeighbors (k := 2) (n := 1) (fun _ => 0)).card = 2 :=
  DeBruijn.outDegree 2 1 _

-- in-degree of any window in `B(3,2)` is `3`.
example : (DeBruijn.inNeighbors (k := 3) (n := 1) (fun _ => 0)).card = 3 :=
  DeBruijn.inDegree 3 1 _

end StdLib
end Graphplay
