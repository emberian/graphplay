import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
open Polynomial Matrix
noncomputable section
def pcm (n : ℕ) : Matrix (Fin n) (Fin n) (Polynomial ℂ) :=
  fun i j => if i = j then X else if (i.val + 1 = j.val ∨ j.val + 1 = i.val) then -1 else 0
lemma pcm_apply (n : ℕ) (i j : Fin n) :
    pcm n i j = if i.val = j.val then X
      else if (i.val + 1 = j.val ∨ j.val + 1 = i.val) then -1 else 0 := by
  simp only [pcm, Fin.ext_iff]
example (n : ℕ) (i' : Fin n) :
    ((pcm (n + 2)).submatrix Fin.succ ((1 : Fin (n+2)).succAbove)) i'.succ 0 = 0 := by
  rw [Matrix.submatrix_apply, Fin.one_succAbove_zero, pcm_apply]
  simp only [Fin.val_succ, Fin.val_zero]
  rw [if_neg (by omega), if_neg (by omega)]
end
