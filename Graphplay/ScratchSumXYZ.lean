import Mathlib.Data.Finset.NoncommProd
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian

open scoped Matrix
open Finset

theorem noncommProd_two_sum {M : Type*} [Ring M] {V : Type*} [Fintype V] [DecidableEq V]
    (e : V → ZMod 2 → M)
    (hc : ∀ (v : V) (b : ZMod 2) (w : V) (c : ZMod 2), Commute (e v b) (e w c))
    (t : Finset V) :
    ∑ s : V → ZMod 2,
        t.noncommProd (fun v => e v (s v))
          (fun v _ w _ _ => hc v (s v) w (s w))
      = (2 ^ (Finset.univ \ t).card) •
          t.noncommProd (fun v => e v 0 + e v 1)
            (fun v _ w _ _ => (Commute.add_left (hc v 0 w 0) (hc v 1 w 0)).add_right
                (Commute.add_left (hc v 0 w 1) (hc v 1 w 1))) := by
  classical
  induction t using Finset.induction with
  | empty =>
    simp only [Finset.noncommProd_empty, Finset.sdiff_empty]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_pi]
    simp [ZMod.card]
  | @insert a t ha ih =>
    set g : V → M := fun v => e v 0 + e v 1 with hg
    have gcomm : ∀ v ∈ (insert a t : Finset V), ∀ w ∈ (insert a t : Finset V), v ≠ w →
        Commute (g v) (g w) := fun v _ w _ _ =>
      (Commute.add_left (hc v 0 w 0) (hc v 1 w 0)).add_right
        (Commute.add_left (hc v 0 w 1) (hc v 1 w 1))
    -- The product over `insert a t` factors out the `a`-factor.
    -- For each sector `s`, write `s = funSplitAt`.
    have key : ∀ s : V → ZMod 2,
        (insert a t).noncommProd (fun v => e v (s v))
          (fun v _ w _ _ => hc v (s v) w (s w))
          = e a (s a) * t.noncommProd (fun v => e v (s v))
              (fun v _ w _ _ => hc v (s v) w (s w)) := by
      intro s
      rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha]
    simp_rw [key]
    -- RHS: peel `a` off the product `g`-noncommProd.
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha]
    -- The inner product over `t` depends only on `s` restricted away from `a`.
    -- Split each `s` via `funSplitAt a`.
    -- Let `Pt s' := t.noncommProd (fun v => e v (s' v)) _` for `s' : V → ZMod 2`,
    -- noting it is invariant under changing the `a`-coordinate.
    have hPt : ∀ s₁ s₂ : V → ZMod 2, (∀ v ∈ t, s₁ v = s₂ v) →
        t.noncommProd (fun v => e v (s₁ v)) (fun v _ w _ _ => hc v (s₁ v) w (s₁ w))
        = t.noncommProd (fun v => e v (s₂ v)) (fun v _ w _ _ => hc v (s₂ v) w (s₂ w)) := by
      intro s₁ s₂ h
      apply Finset.noncommProd_congr rfl
      intro v hv
      rw [h v hv]
    -- The fiber sum K (over `s` with `s a = b`) is independent of `b`.
    -- Use the splitting equiv to reindex the sum over `s` as `(b, s')`.
    sorry
