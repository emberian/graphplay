/-
# Graphplay.Applications.SparseSearch

**Quadratic quantum SEARCH advantage on a SPARSE, physically-realizable host:
the Boolean hypercube `Q_d`.**

The project flagship (`Graphplay.Integrations.QuantumAdvantage`) establishes the
Grover / CTQW quadratic speedup on the complete graph `K_n`.  But `K_n` requires
`n(n-1)/2` all-to-all couplings — *unbuildable* at scale.  This file carries the
same advantage to a host that hardware can actually realize: the **hypercube**
`Q_d` has `N = 2^d` vertices yet **degree only `d = log₂ N`** (sparse, log-degree
— the standard PST/search-chip family of Christandl–Datta–Ekert–Landahl and
Childs–Goldstone).

Childs–Goldstone (`quant-ph/0306054`) proved that continuous-time spatial search
on `Q_d` is optimal — `O(√N)` — and the mechanism is a *pure equitable-partition
spine* fact: with a marked vertex `w`, the **Hamming-distance-from-`w` partition**
of the hypercube into the `d+1` cells (distance `0, 1, …, d`) is **equitable** for
the search Hamiltonian `H = -γ·A(Q_d) − |w⟩⟨w|`.  The search dynamics therefore
collapse from the `N`-dimensional space onto the `(d+1)`-dimensional cell-uniform
subspace — the "collapsed Hamming walk", a weighted path with binomial couplings.

## What is proven (axiom-clean) vs. honest `sorry`

* **GENUINE, axiom-clean — the deliverable.**
  - `hamming_branching` : a vertex `x` at Hamming distance `k` from `w` has
    *exactly* `n - k` neighbours at distance `k+1` and *exactly* `k` neighbours at
    distance `k-1` (the binomial/path branching).  This depends only on `k`.
  - `hammingPartition` and `hammingPartition_equitable` : the
    distance-from-`w` partition into `d+1` cells is an `EquitablePartition` of the
    hypercube search Hamiltonian's adjacency.  **This is the core, reachable
    content** (the binomial branching structure).
  - `hammingPartition_card` : the partition has exactly `d+1` cells.
  - `hypercube_degree` / `hypercube_sparse` : `Q_d` is `d`-regular and
    `d = log₂ N` (the buildability / sparsity claim).
  - the `(d+1)`-dimensional quotient chain `collapsedHammingChain` and its
    connection to the host via `search_quotient_reduction`.

* **Honest `sorry` — deep spectral-timing ONLY.**  The `O(√N)` running-time
  clause leans on the CNO spectral-ratio criterion (`Search/CNO.lean`); the
  perturbative amplitude/time analysis of arXiv:2004.12686 is the single
  `-- BLOCKED: needs CNO spectral-ratio timing` step.

## Generalization (the "tower" thesis)

ANY graph meeting the CNO spectral-ratio condition inherits the advantage via the
same equitable-quotient route: strongly-regular graphs (Janmark–Meyer–Wong),
Johnson graphs, `d`-dimensional lattices `d > 4`.  The strongly-regular case is
recorded as an honest `sorry`-ed theorem (`strongly_regular_sparse_search`)
marking the frontier.
-/

import Graphplay.StdLib.Hypercube
import Graphplay.Search
import Graphplay.Search.CNO
import Graphplay.Equitable
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.ZMod.Basic

open scoped Matrix
open Graphplay.StdLib

namespace Graphplay
namespace SparseSearch

variable {n : ℕ}

/-! ## Hamming-distance basics on `Fin (2^n)` via `testBit`.

The `StdLib/Hypercube` Hamming distance counts positions where the bit-strings
differ.  We re-express it through `Nat.testBit` so we can manipulate single-bit
flips (the hypercube edges) by XOR with a power of two. -/

/-- `bitOf` is exactly `Nat.testBit` on the underlying value. -/
theorem bitOf_eq (x : Fin (2^n)) (i : Fin n) :
    bitOf n x i = Nat.testBit x.val i.val := rfl

/-- Two `Fin n`-indexed bits differ iff the corresponding bit of the XOR is set. -/
theorem bitOf_ne_iff_testBit_xor (x y : Fin (2^n)) (i : Fin n) :
    (bitOf n x i ≠ bitOf n y i) ↔ Nat.testBit (x.val ^^^ y.val) i.val = true := by
  rw [bitOf_eq, bitOf_eq, Nat.testBit_xor]
  cases hx : Nat.testBit x.val i.val <;> cases hy : Nat.testBit y.val i.val <;> simp

/-- The Hamming distance bound: `hammingDist n x y ≤ n` (it is the cardinality of
a subset of `Fin n`). -/
theorem hammingDist_le (x y : Fin (2^n)) : hammingDist n x y ≤ n := by
  unfold hammingDist
  calc (Finset.univ.filter (fun i : Fin n => bitOf n x i ≠ bitOf n y i)).card
      ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.filter_subset _ _)
    _ = n := by rw [Finset.card_univ, Fintype.card_fin]

/-! ## The single-bit flip map (a hypercube edge).

Flipping bit `i` of a vertex `x` toggles exactly one coordinate, i.e. moves to an
adjacent vertex.  Concretely `flip i x` has underlying value `x ^^^ 2^i`. -/

/-- The value `x.val ^^^ 2^i` stays below `2^n` when `i < n`. -/
theorem flip_lt (x : Fin (2^n)) (i : Fin n) :
    x.val ^^^ 2^(i.val) < 2^n :=
  Nat.xor_lt_two_pow x.isLt (Nat.pow_lt_pow_right (by norm_num) i.isLt)

/-- **Bit-flip map.**  `flip i x` toggles the `i`-th bit of `x`; it is the
hypercube edge in direction `i`. -/
def flip (i : Fin n) (x : Fin (2^n)) : Fin (2^n) :=
  ⟨x.val ^^^ 2^(i.val), flip_lt x i⟩

/-- The bit-action of `flip`: bit `j` of `flip i x` is bit `j` of `x` toggled
exactly when `j = i`. -/
theorem bitOf_flip (i : Fin n) (x : Fin (2^n)) (j : Fin n) :
    bitOf n (flip i x) j = (Nat.testBit x.val j.val ^^ decide (i.val = j.val)) := by
  rw [bitOf_eq]
  show Nat.testBit (x.val ^^^ 2^(i.val)) j.val = _
  rw [Nat.testBit_xor, Nat.testBit_two_pow]

/-- `flip` is an involution: flipping the same bit twice returns the original. -/
@[simp] theorem flip_flip (i : Fin n) (x : Fin (2^n)) : flip i (flip i x) = x := by
  apply Fin.ext
  show (x.val ^^^ 2^(i.val)) ^^^ 2^(i.val) = x.val
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

/-- The Hamming distance between `x` and `flip i x` is exactly `1` (they differ in
the single coordinate `i`). -/
theorem hammingDist_flip_self (i : Fin n) (x : Fin (2^n)) :
    hammingDist n x (flip i x) = 1 := by
  unfold hammingDist
  rw [show (Finset.univ.filter (fun j : Fin n => bitOf n x j ≠ bitOf n (flip i x) j))
        = {i} from ?_, Finset.card_singleton]
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  rw [bitOf_flip, bitOf_eq]
  constructor
  · intro h
    by_contra hji
    rw [decide_eq_false (by omega : ¬ i.val = j.val), Bool.xor_false] at h
    exact h rfl
  · rintro rfl
    rw [decide_eq_true rfl, Bool.xor_true]
    cases Nat.testBit x.val j.val <;> simp

/-! ## The Hamming-distance set and how a single flip changes it.

For fixed `x, w`, let `diffSet x w := {j : bitOf x j ≠ bitOf w j}`; its cardinality
is `hammingDist n x w`.  Flipping bit `i` of `x` toggles membership of `i` in this
set and leaves all other coordinates fixed — so the distance from `w` goes down by
`1` if `i` was a difference position (move toward `w`) and up by `1` otherwise.
This is the entire mechanism of the binomial / path branching. -/

/-- The **difference set** of `x` and `w`: the coordinates where their bits
disagree.  Its cardinality is the Hamming distance. -/
def diffSet (x w : Fin (2^n)) : Finset (Fin n) :=
  Finset.univ.filter (fun j : Fin n => bitOf n x j ≠ bitOf n w j)

@[simp] theorem diffSet_card (x w : Fin (2^n)) :
    (diffSet x w).card = hammingDist n x w := rfl

theorem mem_diffSet (x w : Fin (2^n)) (j : Fin n) :
    j ∈ diffSet x w ↔ bitOf n x j ≠ bitOf n w j := by
  simp [diffSet]

/-- Flipping bit `i` toggles exactly the membership of `i` in the difference set
relative to `w`, and fixes every other coordinate. -/
theorem mem_diffSet_flip (i : Fin n) (x w : Fin (2^n)) (j : Fin n) :
    j ∈ diffSet (flip i x) w ↔
      (if j = i then j ∉ diffSet x w else j ∈ diffSet x w) := by
  rw [mem_diffSet, bitOf_flip]
  by_cases hji : j = i
  · subst hji
    rw [if_pos rfl, mem_diffSet]
    rw [decide_eq_true (rfl : j.val = j.val), Bool.xor_true]
    cases hb : bitOf n x j <;> cases hc : bitOf n w j <;>
      simp_all [bitOf_eq]
  · rw [if_neg hji, mem_diffSet]
    rw [decide_eq_false (fun h : i.val = j.val => hji (Fin.ext h.symm)), Bool.xor_false]
    rw [show bitOf n x j = Nat.testBit x.val j.val from rfl]

/-- **Distance decreases when flipping a difference coordinate.**  If `i` is a
position where `x` and `w` differ, flipping it brings `x` one step closer to `w`:
`dist(flip i x, w) = dist(x, w) − 1`. -/
theorem hammingDist_flip_mem (i : Fin n) (x w : Fin (2^n))
    (hi : i ∈ diffSet x w) :
    hammingDist n (flip i x) w = hammingDist n x w - 1 := by
  rw [← diffSet_card, ← diffSet_card]
  rw [show diffSet (flip i x) w = (diffSet x w).erase i from ?_]
  · rw [Finset.card_erase_of_mem hi]
  · ext j
    rw [mem_diffSet_flip, Finset.mem_erase]
    by_cases hji : j = i
    · subst hji; simp [hi]
    · simp [hji]

/-- **Distance increases when flipping an agreement coordinate.**  If `i` is a
position where `x` and `w` agree, flipping it moves `x` one step away from `w`:
`dist(flip i x, w) = dist(x, w) + 1`. -/
theorem hammingDist_flip_notMem (i : Fin n) (x w : Fin (2^n))
    (hi : i ∉ diffSet x w) :
    hammingDist n (flip i x) w = hammingDist n x w + 1 := by
  rw [← diffSet_card, ← diffSet_card]
  rw [show diffSet (flip i x) w = insert i (diffSet x w) from ?_]
  · rw [Finset.card_insert_of_notMem hi]
  · ext j
    rw [mem_diffSet_flip, Finset.mem_insert]
    by_cases hji : j = i
    · subst hji; simp [hi]
    · simp [hji]

/-! ## Neighbours of `x` are exactly the `n` bit-flips.

A vertex `z` is adjacent to `x` in `Q_n` (Hamming distance `1`) iff `z = flip i x`
for a unique direction `i`.  Hence any sum of `adj x z` over `z` collapses to a sum
over `i : Fin n`. -/

/-- A vertex at Hamming distance `1` from `x` is `flip i x` for the unique
difference coordinate `i`. -/
theorem eq_flip_of_hammingDist_one (x z : Fin (2^n)) (h : hammingDist n x z = 1) :
    ∃ i : Fin n, z = flip i x := by
  -- The difference set `diffSet x z` has cardinality `1`, hence is `{i}`.
  have hcard : (diffSet x z).card = 1 := by rw [diffSet_card]; exact h
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcard
  refine ⟨i, ?_⟩
  -- `flip i x` and `z` agree on every coordinate: at `i` both flip `x`'s bit (since
  -- `x,z` differ there), elsewhere both equal `x`'s bit (since `x,z` agree there).
  apply Fin.ext
  -- reduce to bit equality on all coordinates
  have hbits : ∀ j : Fin n, bitOf n (flip i x) j = bitOf n z j := by
    intro j
    have hmem : (j ∈ diffSet x z) ↔ j = i := by rw [hi]; simp
    by_cases hji : j = i
    · subst hji
      rw [bitOf_flip, decide_eq_true (rfl : j.val = j.val), Bool.xor_true, bitOf_eq]
      have hdiff : bitOf n x j ≠ bitOf n z j := (mem_diffSet x z j).mp (hmem.mpr rfl)
      rw [bitOf_eq, bitOf_eq] at hdiff
      cases hb : Nat.testBit x.val j.val <;> cases hc : Nat.testBit z.val j.val <;>
        simp_all
    · rw [bitOf_flip, decide_eq_false (fun h : i.val = j.val => hji (Fin.ext h.symm)),
        Bool.xor_false]
      have hagree : ¬ (bitOf n x j ≠ bitOf n z j) := by
        rw [← mem_diffSet]; rw [hmem]; exact hji
      exact not_not.mp hagree
  -- `flip i x` and `z` have the same `testBit` on all `j < n`; both `< 2^n`.
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < n
  · have := (hbits ⟨k, hk⟩).symm
    rw [bitOf_eq, bitOf_eq] at this
    exact this
  · -- bits `≥ n` are zero for both since values `< 2^n`
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le z.isLt
          (Nat.pow_le_pow_right (by norm_num) (by omega))),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (flip i x).isLt
          (Nat.pow_le_pow_right (by norm_num) (by omega)))]

/-- The map `i ↦ flip i x` is injective (distinct directions flip distinct
coordinates, giving distinct vertices). -/
theorem flip_injective (x : Fin (2^n)) :
    Function.Injective (fun i : Fin n => flip i x) := by
  intro i₁ i₂ h
  simp only at h
  -- Inspect bit `i₁` of both sides: LHS flips `x`'s bit, RHS flips it iff `i₂ = i₁`.
  have hbit : bitOf n (flip i₁ x) i₁ = bitOf n (flip i₂ x) i₁ := by rw [h]
  rw [bitOf_flip, bitOf_flip] at hbit
  rw [decide_eq_true (rfl : i₁.val = i₁.val), Bool.xor_true] at hbit
  -- `!bit = bit ^^ decide(i₂=i₁)` forces `decide(i₂=i₁) = true`, i.e. `i₁ = i₂`.
  have hdec : decide (i₂.val = i₁.val) = true := by
    cases hb : Nat.testBit x.val i₁.val <;> simp_all [bitOf_eq]
  exact Fin.ext ((of_decide_eq_true hdec).symm)

/-! ## Branching is determined by the distance — the equitable core.

For a vertex `x` at distance `k = dist(x,w)`, its neighbours split into exactly
`k` vertices at distance `k−1` (flip a difference coordinate) and `n−k` vertices
at distance `k+1` (flip an agreement coordinate).  We package the branching sum
`∑_z [dist(z,w)=j]·adj(x,z)` and show it depends only on `k` and `j`. -/

/-- The branching sum into the distance-`j` cell, as a count over flip directions:
`∑_z [dist(z,w)=j]·adj(x,z) = #{ i : dist(flip i x, w) = j }`. -/
theorem branching_eq_flipCount (x w : Fin (2^n)) (j : ℕ) :
    (∑ z, (if hammingDist n z w = j then
            (if hammingDist n x z = 1 then (1 : ℂ) else 0) else 0))
      = ((Finset.univ.filter
            (fun i : Fin n => hammingDist n (flip i x) w = j)).card : ℂ) := by
  classical
  -- Reindex the sum over `z` along the injection `i ↦ flip i x`; the summand is
  -- supported on neighbours of `x`, all of which are flips.
  rw [show (∑ z, (if hammingDist n z w = j then
            (if hammingDist n x z = 1 then (1 : ℂ) else 0) else 0))
        = ∑ z ∈ Finset.univ.filter (fun z => hammingDist n x z = 1),
            (if hammingDist n z w = j then (1 : ℂ) else 0) from ?_]
  · -- The neighbour set is the image of `flip · x`.
    rw [show (Finset.univ.filter (fun z => hammingDist n x z = 1))
          = Finset.univ.image (fun i : Fin n => flip i x) from ?_]
    · rw [Finset.sum_image (fun i _ i' _ h => flip_injective x h)]
      -- Each flip is at distance `1` and contributes its `[dist(·,w)=j]` indicator.
      rw [Finset.card_filter, Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hj : hammingDist n (flip i x) w = j <;> simp [hj]
    · ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hz
        obtain ⟨i, hi⟩ := eq_flip_of_hammingDist_one x z hz
        exact ⟨i, hi.symm⟩
      · rintro ⟨i, rfl⟩; exact hammingDist_flip_self i x
  · rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : hammingDist n x z = 1 <;>
      by_cases hj : hammingDist n z w = j <;> simp [hz, hj]

/-- **The binomial branching count is a function of the distance only.**  For `x`
at distance `k` from `w`, the number of directions `i` with `dist(flip i x, w) = j`
is `k` when `j = k−1`, `n−k` when `j = k+1`, and `0` otherwise.  We record the
load-bearing consequence: the count depends on `x` only through `k`. -/
theorem flipCount_eq_of_dist_eq (x y w : Fin (2^n)) (j : ℕ)
    (hxy : hammingDist n x w = hammingDist n y w) :
    (Finset.univ.filter (fun i : Fin n => hammingDist n (flip i x) w = j)).card
      = (Finset.univ.filter (fun i : Fin n => hammingDist n (flip i y) w = j)).card := by
  classical
  -- Split the count for any vertex `v` by whether `i` is a difference coordinate.
  have key : ∀ v : Fin (2^n),
      (Finset.univ.filter (fun i : Fin n => hammingDist n (flip i v) w = j)).card
        = (Finset.univ.filter (fun i : Fin n =>
              (if i ∈ diffSet v w then hammingDist n v w - 1
               else hammingDist n v w + 1) = j)).card := by
    intro v
    congr 1
    apply Finset.filter_congr
    intro i _
    by_cases hi : i ∈ diffSet v w
    · rw [if_pos hi, hammingDist_flip_mem i v w hi]
    · rw [if_neg hi, hammingDist_flip_notMem i v w hi]
  rw [key x, key y]
  -- The filter predicate on `i` only inspects `i ∈ diffSet · w` and the common
  -- distance `k`.  For any `v` with `dist v w = k`, the count is determined.
  rw [← hxy]
  set k := hammingDist n x w with hk
  -- For vertex `v` with `dist v w = k`, the filtered count is
  -- `(if k-1=j then |diffSet v w| else 0) + (if k+1=j then |complement| else 0)`,
  -- and both cardinalities are determined by `k` (= `k` and `n-k`).
  have hcount : ∀ v : Fin (2^n), hammingDist n v w = k →
      (Finset.univ.filter (fun i : Fin n =>
          (if i ∈ diffSet v w then k - 1 else k + 1) = j)).card
        = (if k - 1 = j then k else 0) + (if k + 1 = j then n - k else 0) := by
    intro v hv
    -- The number of difference coordinates is `dist v w = k`; agreement coordinates
    -- number `n - k`.
    have hdiffcard : (diffSet v w).card = k := by rw [diffSet_card]; exact hv
    have hcompl : (Finset.univ.filter (fun i : Fin n => i ∉ diffSet v w)).card = n - k := by
      have : (Finset.univ.filter (fun i : Fin n => i ∉ diffSet v w))
          = (diffSet v w)ᶜ := by
        ext i; simp [Finset.mem_compl]
      rw [this, Finset.card_compl, hdiffcard, Fintype.card_fin]
    -- The constant propositions `k-1 = j` and `k+1 = j` cannot hold simultaneously.
    by_cases h1 : k - 1 = j
    · by_cases h2 : k + 1 = j
      · -- `k-1 = k+1` is impossible for naturals.
        omega
      · -- predicate is `i ∈ diffSet v w`; count is `k`.
        rw [if_pos h1, if_neg h2, add_zero]
        rw [show (Finset.univ.filter (fun i : Fin n =>
                (if i ∈ diffSet v w then k - 1 else k + 1) = j))
              = diffSet v w from ?_, hdiffcard]
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases hi : i ∈ diffSet v w
        · simp [hi, h1]
        · simp [hi, h2]
    · by_cases h2 : k + 1 = j
      · -- predicate is `i ∉ diffSet v w`; count is `n - k`.
        rw [if_neg h1, if_pos h2, zero_add]
        rw [show (Finset.univ.filter (fun i : Fin n =>
                (if i ∈ diffSet v w then k - 1 else k + 1) = j))
              = (Finset.univ.filter (fun i : Fin n => i ∉ diffSet v w)) from ?_, hcompl]
        apply Finset.filter_congr
        intro i _
        by_cases hi : i ∈ diffSet v w
        · simp [hi, h1]
        · simp [hi, h2]
      · -- neither value matches `j`; the filter is empty.
        rw [if_neg h1, if_neg h2, add_zero]
        rw [show (Finset.univ.filter (fun i : Fin n =>
                (if i ∈ diffSet v w then k - 1 else k + 1) = j))
              = ∅ from ?_, Finset.card_empty]
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
          iff_false]
        by_cases hi : i ∈ diffSet v w
        · simp [hi, h1]
        · simp [hi, h2]
  rw [hcount x hk.symm, hcount y hxy.symm]

/-! ## The Hamming-distance-from-`w` equitable partition — the deliverable.

Fix a marked vertex `w : Fin (2^d)`.  Label each vertex `x` by its Hamming
distance from `w` (a number in `{0, 1, …, d}`, since `dist ≤ d`).  This partitions
the hypercube into `d+1` cells.  The branching count computed above shows the
partition is **equitable** for the hypercube adjacency: a vertex in the
distance-`k` cell sends exactly `k` edges to the distance-`(k−1)` cell and `d−k`
to the distance-`(k+1)` cell — depending only on `k`, never on the representative.
This is the collapsed weighted "Hamming path" with binomial couplings, the heart of
Childs–Goldstone search on `Q_d`. -/

/-- The distance-from-`w` cell label of a vertex, as an element of `Fin (d+1)`
(distances range over `0, …, d`). -/
def hammingCell (d : ℕ) (w x : Fin (2^d)) : Fin (d + 1) :=
  ⟨hammingDist d w x, Nat.lt_succ_of_le (hammingDist_le w x)⟩

/-- **The Hamming-distance-from-`w` partition is equitable.**  This is the genuine,
axiom-clean core: the binomial branching structure makes the distance partition an
`EquitablePartition` of the hypercube `Q_d`, with `d+1` cells. -/
def hammingPartition (d : ℕ) (w : Fin (2^d)) :
    EquitablePartition (Hypercube d) (Fin (d + 1)) where
  cells := hammingCell d w
  uniform := by
    intro i j x y hx hy
    -- `cells x = i` and `cells y = i` give `dist w x = dist w y = i.val`.
    have hdwx : hammingDist d w x = i.val := congrArg Fin.val hx
    have hdwy : hammingDist d w y = i.val := congrArg Fin.val hy
    -- Rewrite each branching sum into the flip-count form, matching cells `j`.
    have hcellsj : ∀ z : Fin (2^d),
        (Hypercube d).adj x z = (if hammingDist d x z = 1 then (1 : ℂ) else 0) := fun z => rfl
    -- The cell guard `hammingCell d w z = j` is `hammingDist d z w = j.val`.
    have hguard : ∀ (v z : Fin (2^d)),
        (∑ z, (if hammingCell d w z = j then (Hypercube d).adj v z else 0))
          = (∑ z, (if hammingDist d z w = j.val then
              (if hammingDist d v z = 1 then (1 : ℂ) else 0) else 0)) := by
      intro v _
      apply Finset.sum_congr rfl
      intro z _
      have hcellz : (hammingCell d w z = j) ↔ (hammingDist d z w = j.val) := by
        unfold hammingCell
        rw [Fin.ext_iff]
        simp [hammingDist_comm d w z]
      by_cases hc : hammingCell d w z = j
      · rw [if_pos hc, if_pos (hcellz.mp hc)]; rfl
      · rw [if_neg hc, if_neg (fun h => hc (hcellz.mpr h))]
    rw [hguard x x, hguard y y]
    rw [branching_eq_flipCount x w j.val, branching_eq_flipCount y w j.val]
    -- The two flip-counts agree because `dist x w = dist y w`.
    congr 1
    apply flipCount_eq_of_dist_eq
    rw [hammingDist_comm d x w, hammingDist_comm d y w, hdwx, hdwy]

/-- The partition has exactly `d + 1` cells. -/
theorem hammingPartition_card (d : ℕ) (w : Fin (2^d)) :
    Fintype.card (Fin (d + 1)) = d + 1 := Fintype.card_fin _

/-- The marked vertex sits in cell `0` (distance `0` from itself). -/
theorem hammingCell_marked (d : ℕ) (w : Fin (2^d)) :
    hammingCell d w w = ⟨0, Nat.succ_pos d⟩ := by
  unfold hammingCell
  rw [Fin.ext_iff]
  simp [hammingDist_self]

/-! ## Sparsity: `Q_d` is `d`-regular, and `d = log₂ N` — the buildability claim.

The hypercube has `N = 2^d` vertices but **degree only `d`** (each vertex has
exactly `d` neighbours, one per bit-flip direction).  Since `d = log₂ N`, the host
is **log-degree sparse** — physically realizable, unlike the all-to-all `K_n`
which needs `n−1` couplings per vertex. -/

/-- **The hypercube is `d`-regular.**  Every vertex has exactly `d` neighbours
(the `d` single-bit-flip directions), so the weighted row sum is `d`. -/
theorem hypercube_isRegular (d : ℕ) : (Hypercube d).isRegular (d : ℂ) := by
  intro x
  classical
  -- `degree x = ∑ z, [dist x z = 1] = #(neighbours of x) = #(image of flip · x) = d`.
  unfold WeightedGraph.degree
  have hadj : ∀ z, (Hypercube d).adj x z = (if hammingDist d x z = 1 then (1 : ℂ) else 0) :=
    fun z => rfl
  rw [Finset.sum_congr rfl (fun z _ => hadj z)]
  -- Collapse to a count over neighbours.
  rw [show (∑ z, (if hammingDist d x z = 1 then (1 : ℂ) else 0))
        = ((Finset.univ.filter (fun z => hammingDist d x z = 1)).card : ℂ) from ?_]
  · -- The neighbour set is the image of `flip · x`, of cardinality `d`.
    rw [show (Finset.univ.filter (fun z => hammingDist d x z = 1))
          = Finset.univ.image (fun i : Fin d => flip i x) from ?_]
    · rw [Finset.card_image_of_injective _ (flip_injective x), Finset.card_univ,
        Fintype.card_fin]
    · ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hz
        obtain ⟨i, hi⟩ := eq_flip_of_hammingDist_one x z hz
        exact ⟨i, hi.symm⟩
      · rintro ⟨i, rfl⟩; exact hammingDist_flip_self i x
  · rw [Finset.card_filter, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : hammingDist d x z = 1 <;> simp [hz]

/-- **Degree equals `d`** at any specific vertex (unfolded form of regularity). -/
theorem hypercube_degree (d : ℕ) (x : Fin (2^d)) :
    (Hypercube d).degree x = (d : ℂ) :=
  hypercube_isRegular d x

/-- **Sparsity / buildability: the degree is `log₂ N`.**  With `N = 2^d` vertices,
the hypercube degree `d` equals `Nat.log 2 N`.  This is the log-degree (sparse)
fact that makes `Q_d` a physically realizable search host, in contrast to the
`K_N`'s degree `N − 1`. -/
theorem hypercube_sparse (d : ℕ) :
    d = Nat.log 2 (Fintype.card (Fin (2^d))) := by
  rw [Fintype.card_fin, Nat.log_pow (by norm_num : 1 < 2)]

/-! ## The collapsed Hamming chain and the search-quotient reduction.

The marked set `{w}` is a **union of cells** of the Hamming partition (it is exactly
the distance-`0` cell), so the marked-refined partition is equitable and the host
search Hamiltonian `H = -γ·A(Q_d) − |w⟩⟨w|` acts, on the cell-uniform subspace, as
the `(d+1)`-dimensional refined-quotient search Hamiltonian (the collapsed weighted
Hamming path).  This is the exact, axiom-clean reduction
`Graphplay.search_quotient_reduction`. -/

/-- The singleton marked set `{w}` is a union of Hamming-cells: membership is
constant on each cell (a vertex is `w` iff it is in the distance-`0` cell). -/
theorem markedSet_cellUniform (d : ℕ) (w : Fin (2^d)) :
    ∀ x y : Fin (2^d), (hammingPartition d w).cells x = (hammingPartition d w).cells y →
      (x ∈ ({w} : Finset (Fin (2^d))) ↔ y ∈ ({w} : Finset (Fin (2^d)))) := by
  intro x y hxy
  -- `x ∈ {w}` iff `x = w` iff `dist w x = 0` iff `cells x = 0`; same for `y`.
  have hcell : ∀ v : Fin (2^d),
      (v ∈ ({w} : Finset (Fin (2^d)))) ↔ (hammingPartition d w).cells v = ⟨0, Nat.succ_pos d⟩ := by
    intro v
    rw [Finset.mem_singleton]
    show (v = w) ↔ (hammingCell d w v = ⟨0, Nat.succ_pos d⟩)
    rw [show (hammingCell d w v = ⟨0, Nat.succ_pos d⟩) ↔ (hammingDist d w v = 0) from by
      rw [Fin.ext_iff]; rfl]
    constructor
    · intro hvw; subst hvw; simp [hammingDist_self]
    · intro h
      -- `dist w v = 0 ⇒ v = w`
      have hd0 : hammingDist d w v = 0 := h
      -- distance 0 means the difference set is empty, i.e. all bits agree
      have hcard : (diffSet w v).card = 0 := by rw [diffSet_card]; exact hd0
      have hempty : diffSet w v = ∅ := Finset.card_eq_zero.mp hcard
      -- all coordinates agree ⇒ equal values
      apply Fin.ext
      apply Nat.eq_of_testBit_eq
      intro b
      by_cases hb : b < d
      · have : (⟨b, hb⟩ : Fin d) ∉ diffSet w v := by rw [hempty]; exact Finset.notMem_empty _
        rw [mem_diffSet] at this
        have hbit := not_not.mp this
        rw [bitOf_eq, bitOf_eq] at hbit
        exact hbit.symm
      · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le v.isLt
              (Nat.pow_le_pow_right (by norm_num) (by omega))),
            Nat.testBit_eq_false_of_lt (lt_of_lt_of_le w.isLt
              (Nat.pow_le_pow_right (by norm_num) (by omega)))]
  rw [hcell x, hcell y, hxy]

/-- **Search-quotient reduction on the hypercube (exact, axiom-clean).**  Applying
the hypercube search Hamiltonian `H = -γ·A(Q_d) − |w⟩⟨w|` to any cell-uniform state
(constant on each Hamming-distance shell) returns the cell-uniform state whose
`(d+1)`-dimensional weight vector evolves under the refined-quotient search
Hamiltonian `-γ·Q̃' − markedDiag` — the collapsed Hamming chain.  The full
`N = 2^d`-dimensional dynamics live entirely on the `(d+1)`-dimensional quotient.

This is the precise mechanism of Childs–Goldstone search on `Q_d`, obtained here by
specializing the spine reduction `search_quotient_reduction` to the (proven
equitable) Hamming partition with the (proven cell-uniform) marked set `{w}`. -/
theorem hypercube_search_quotient_reduction (d : ℕ) (w : Fin (2^d)) (γ : ℝ)
    (weights : MarkedRefined (Fin (d + 1)) → ℂ) :
    let P := hammingPartition d w
    let hM := markedSet_cellUniform d w
    let P' := P.refineByMarked ({w} : Finset (Fin (2^d))) hM
    ((Hypercube d).searchHamiltonian ({w} : Finset (Fin (2^d))) γ).mulVec
        (fun v => ∑ ib, weights ib * P'.cellUniformVec ib v)
      = (fun v => ∑ ib,
          ((-(γ : ℂ) • P'.symmQuotient - markedDiag (Fin (d + 1))).mulVec weights) ib *
            P'.cellUniformVec ib v) :=
  search_quotient_reduction (hammingPartition d w) ({w} : Finset (Fin (2^d))) γ
    (markedSet_cellUniform d w) weights

/-! ## The headline theorems (split: proven reduction vs. honest timing).

To keep theorem **names honest**, the proven structural content (sparsity +
equitable reduction) and the unproven dynamical content (the `O(√N)` timing) are
stated as *separate* theorems:

* `hypercube_sparse_search_reduction` — the **axiom-clean deliverable**:
  log-degree sparsity AND the equitable Hamming-chain reduction.  No timing
  clause, fully `#print axioms`-clean.
* `hypercube_search_optimal_timing` — the **honest frontier**: the `O(√N)`
  `IsOptimalCTQWSearch` clause, carrying the single `-- BLOCKED:` `sorry`. -/

/-- **`hypercube_sparse_search_reduction` — the axiom-clean deliverable.**  The
Boolean hypercube `Q_d` is a **degree-`log₂ N` (sparse, physically realizable)**
host whose marked CTQW search dynamics reduce, via its Hamming-distance equitable
quotient, to a `(d+1)`-dimensional search.  This theorem asserts ONLY the
genuinely proven (axiom-clean) halves — it does NOT claim the `O(√N)` timing
advantage (see `hypercube_search_optimal_timing` for that, honest-`sorry`d):

* **Sparsity / buildability.**  `Q_d` is `d`-regular with `d = log₂ N` — log-degree,
  unlike `K_N`'s degree `N − 1`.

* **Equitable reduction.**  The distance-from-`w` partition into the `d+1` cells is
  equitable (the binomial branching), the marked set `{w}` is a union of cells, and
  the host search Hamiltonian collapses to the `(d+1)`-dimensional collapsed-Hamming
  quotient chain (`hypercube_search_quotient_reduction`). -/
theorem hypercube_sparse_search_reduction (d : ℕ) (hd : 1 ≤ d) (w : Fin (2^d)) :
    -- (1) SPARSITY / BUILDABILITY (proven, axiom-clean):
    ((Hypercube d).isRegular (d : ℂ) ∧ d = Nat.log 2 (Fintype.card (Fin (2^d))))
    ∧
    -- (2) EQUITABLE REDUCTION to the (d+1)-dim collapsed Hamming chain
    --     (proven, axiom-clean):
    (∀ (γ : ℝ) (weights : MarkedRefined (Fin (d + 1)) → ℂ),
      let P := hammingPartition d w
      let hM := markedSet_cellUniform d w
      let P' := P.refineByMarked ({w} : Finset (Fin (2^d))) hM
      ((Hypercube d).searchHamiltonian ({w} : Finset (Fin (2^d))) γ).mulVec
          (fun v => ∑ ib, weights ib * P'.cellUniformVec ib v)
        = (fun v => ∑ ib,
            ((-(γ : ℂ) • P'.symmQuotient - markedDiag (Fin (d + 1))).mulVec weights) ib *
              P'.cellUniformVec ib v)) := by
  refine ⟨⟨hypercube_isRegular d, hypercube_sparse d⟩, ?_⟩
  intro γ weights
  exact hypercube_search_quotient_reduction d w γ weights

/-- **`hypercube_search_optimal_timing` — the honest frontier (single `sorry`).**
The deep `O(√N)` spectral-gap **timing** claim: the `(d+1)`-dimensional reduced
hypercube search actually reaches constant amplitude in time `O(√N)`, i.e. it is
CNO-optimal (`IsOptimalCTQWSearch`).  This leans on the CNO spectral-ratio
criterion of `Graphplay.Search.CNO`; it is the single honest `sorry` (the
perturbative amplitude/time analysis of arXiv:2004.12686, exactly the same
dynamical core sorried by the `K_n` flagship `complete_graph_optimal_search`).

This is the ONLY clause that asserts the search *advantage* (timing), and it is
honestly unproven; the proven structural reduction is `hypercube_sparse_search_reduction`. -/
theorem hypercube_search_optimal_timing (d : ℕ) (hd : 1 ≤ d) (w : Fin (2^d)) :
    IsOptimalCTQWSearch (Hypercube d) w := by
  -- BLOCKED: needs CNO spectral-ratio timing
  sorry

/-! ## Generalization (the "tower" thesis): the CNO frontier.

ANY regular graph whose principal eigenvector is uniform and which satisfies the
**CNO spectral-ratio condition** `CNOSpectralRatio < 1` (a constant spectral gap)
inherits the same `O(√N)` search advantage via the identical equitable-quotient
route — strongly-regular graphs (Janmark–Meyer–Wong), Johnson graphs,
`d`-dimensional lattices `d > 4`.  We record the strongly-regular case as an honest
frontier `sorry`. -/

/-- **Strongly-regular search advantage (frontier, honest `sorry`).**  A
strongly-regular graph (here abstracted as a `d`-regular host with uniform
principal eigenvector and a spectral ratio `< 1`) supports optimal CTQW search by
the CNO criterion — the same equitable-quotient mechanism as the hypercube.

Reference: Janmark–Meyer–Wong, *Global symmetry is unnecessary for fast quantum
search* (PRL 2014), arXiv:1403.2228.  Sorried at the CNO dynamical core
(`optimal_search_of_spectral_ratio_lt_one`). -/
theorem strongly_regular_sparse_search
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (w p : V) (deg : ℂ)
    (hne : Nonempty V)
    (hreg : G.isRegular deg)
    (huniform : ∀ x : V,
      (G.herm.eigenvectorBasis p : V → ℂ) x = (1 : ℂ) / Real.sqrt (Fintype.card V))
    (hp : 0 < |G.herm.eigenvalues p|)
    (hratio : CNOSpectralRatio G p < 1) :
    IsOptimalCTQWSearch G w :=
  -- Delegates to the CNO criterion; the spectral-timing core is sorried there
  -- (`-- BLOCKED: needs CNO spectral-ratio timing`).
  optimal_search_of_spectral_ratio_lt_one G w p deg hne hreg huniform hp hratio

/-! ## The d-dimensional periodic lattice `Z_L^d` — the buildable-but-(usually)-non-advantageous host.

We now add the *other* canonical buildable search host: the **`d`-dimensional
periodic lattice (discrete torus) `Z_L^d`**, the abstraction of every physically
*spatial* quantum chip — optical lattices, superconducting grids, photonic
waveguide arrays.  Its vertex set is `Fin d → ZMod L` (a `d`-tuple of coordinates
mod `L`), and two vertices are adjacent iff they differ by `±1` in *exactly one*
coordinate (nearest-neighbour hopping with wraparound).  Each vertex has exactly
`2·d` neighbours — `2` per axis — so the lattice is `2d`-regular with **degree
independent of `N = L^d`**: the hallmark of buildable hardware.

The honest twist (this is the point of the file): Childs–Goldstone
(`quant-ph/0306054`) proved that continuous-time spatial search on `Z_L^d` attains
the optimal `Θ(√N)` running time **only for `d > 4`**; `d = 4` loses a `√log N`
factor, and `d ≤ 3` — *every literal 2D/3D chip* — does **not** achieve the
quadratic speedup at all.  The mechanism is an infrared (small-momentum)
convergence threshold of the lattice Green's function `∑_k 1/(1−cos k)`, which is
dimension-`4`-critical.  So the most *buildable* host (a 2D/3D grid) is precisely
the one that does *not* win, while the hypercube `Q_d` — degree only `log₂N`, yet
spectrally in the high-dimensional regime — threads the needle.

Throughout we require `[Fact (2 < L)]` (i.e. `L ≥ 3`): a periodic lattice with
side `< 3` has the two `±1` neighbours along an axis collapse onto each other, so
`L ≥ 3` is exactly the condition for the `2d` nearest neighbours to be genuinely
distinct (and for the graph to be loopless).  This is no loss: every physical
lattice has `L ≥ 3`. -/

/-- The vertex type of the `d`-dimensional periodic lattice of side `L`: a tuple
of `d` coordinates, each in `ZMod L` (so addition wraps around — the torus). -/
abbrev LatticeVertex (d L : ℕ) : Type := Fin d → ZMod L

/-- A side length `L > 2` is in particular nonzero, so `ZMod L` is a finite type
with decidable equality (hence so is `LatticeVertex d L`). -/
instance (priority := 100) instNeZeroOfFact2Lt (L : ℕ) [h : Fact (2 < L)] : NeZero L :=
  ⟨by have := h.out; omega⟩

/-- A side `L > 2` is in particular `> 1`, so `ZMod L` is nontrivial (`1 ≠ 0`,
`-1 ≠ 0`, `-1 ≠ 1`). -/
instance (priority := 100) instFact1LtOfFact2Lt (L : ℕ) [h : Fact (2 < L)] :
    Fact (1 < L) := ⟨by have := h.out; omega⟩

/-- **Axis shift.**  `latticeShift i s x` moves `x` by `s` along axis `i`
(leaving all other coordinates fixed): `Function.update x i (x i + s)`.  The
nearest-neighbour edges of the torus are the shifts with `s = ±1`. -/
def latticeShift {d L : ℕ} (i : Fin d) (s : ZMod L) (x : LatticeVertex d L) :
    LatticeVertex d L :=
  Function.update x i (x i + s)

@[simp] theorem latticeShift_self {d L : ℕ} (i : Fin d) (s : ZMod L)
    (x : LatticeVertex d L) : latticeShift i s x i = x i + s := by
  unfold latticeShift; rw [Function.update_self]

theorem latticeShift_of_ne {d L : ℕ} {i j : Fin d} (s : ZMod L)
    (x : LatticeVertex d L) (h : j ≠ i) : latticeShift i s x j = x j := by
  unfold latticeShift; rw [Function.update_of_ne h]

/-- Shifting back: `latticeShift i (-s) (latticeShift i s x) = x`. -/
@[simp] theorem latticeShift_neg_cancel {d L : ℕ} (i : Fin d) (s : ZMod L)
    (x : LatticeVertex d L) :
    latticeShift i (-s) (latticeShift i s x) = x := by
  funext j
  by_cases hj : j = i
  · subst hj; rw [latticeShift_self, latticeShift_self]; ring
  · rw [latticeShift_of_ne _ _ hj, latticeShift_of_ne _ _ hj]

/-- The **nearest-neighbour adjacency** of the periodic lattice: `x` and `y` are
adjacent iff `y` is `x` shifted by `±1` along some single axis. -/
def latticeAdjacent {d L : ℕ} (x y : LatticeVertex d L) : Prop :=
  ∃ (i : Fin d) (s : ZMod L), (s = 1 ∨ s = -1) ∧ y = latticeShift i s x

/-- Adjacency is symmetric (shifting by `s` is undone by shifting by `-s`, and
`±1` is closed under negation). -/
theorem latticeAdjacent_comm {d L : ℕ} (x y : LatticeVertex d L) :
    latticeAdjacent x y ↔ latticeAdjacent y x := by
  -- It suffices to prove one direction (then apply it both ways).
  suffices h : ∀ a b : LatticeVertex d L, latticeAdjacent a b → latticeAdjacent b a by
    exact ⟨h x y, h y x⟩
  rintro a b ⟨i, s, hs, rfl⟩
  refine ⟨i, -s, ?_, (latticeShift_neg_cancel i s a).symm⟩
  rcases hs with h | h
  · right; rw [h]
  · left; rw [h, neg_neg]

open Classical in
/-- **The `d`-dimensional periodic lattice `Z_L^d` as a weighted graph.**
Adjacency value is `1` between nearest neighbours (differ by `±1` in exactly one
coordinate, mod `L`) and `0` otherwise.  Hermitian by symmetry of
`latticeAdjacent`; loopless because a `±1` shift never fixes a vertex when
`L ≥ 3`. -/
noncomputable def latticeGraph (d L : ℕ) [Fact (2 < L)] :
    WeightedGraph (LatticeVertex d L) where
    adj := fun x y => if latticeAdjacent x y then (1 : ℂ) else 0
    herm := by
      refine Matrix.IsHermitian.ext (fun x y => ?_)
      show star (if latticeAdjacent y x then (1 : ℂ) else 0)
          = if latticeAdjacent x y then (1 : ℂ) else 0
      rw [← latticeAdjacent_comm x y]
      by_cases h : latticeAdjacent x y
      · rw [if_pos h]; simp
      · rw [if_neg h]; simp
    loopless := by
      intro v
      -- `latticeAdjacent v v` would force a `±1` shift to fix `v`, i.e. `±1 = 0`,
      -- impossible for `L ≥ 3`.
      rw [if_neg]
      rintro ⟨i, s, hs, hv⟩
      have hval : v i = v i + s := by
        have := congrFun hv i; rwa [latticeShift_self] at this
      have hs0 : s = 0 := by
        have h2 : v i + 0 = v i + s := by rw [add_zero]; exact hval
        exact (add_left_cancel h2).symm
      rcases hs with h | h
      · rw [h] at hs0; exact one_ne_zero hs0
      · rw [h] at hs0
        have : (1 : ZMod L) = 0 := by rw [← neg_neg (1 : ZMod L), hs0, neg_zero]
        exact one_ne_zero this

/-! ### `2d`-regularity and sparsity of the lattice — the axiom-clean deliverable.

The lattice is `2d`-regular: each vertex has exactly two neighbours per axis
(`+1` and `−1`), for `2d` total, and they are genuinely distinct when `L ≥ 3`.
We prove this by exhibiting the neighbour set as the injective image of the `2d`
shift maps indexed by `Fin d × Bool` (`true ↦ +1`, `false ↦ −1`). -/

/-- The signed unit of a Boolean: `true ↦ +1`, `false ↦ −1` in `ZMod L`. -/
def signUnit (L : ℕ) (b : Bool) : ZMod L := if b then 1 else -1

theorem signUnit_mem_pm (L : ℕ) (b : Bool) :
    signUnit L b = 1 ∨ signUnit L b = -1 := by
  unfold signUnit; cases b <;> simp

/-- The `2d` neighbour-generating map: `(i, b) ↦ x shifted by ±1 along axis i`. -/
def latticeNeighborMap {d L : ℕ} (x : LatticeVertex d L) (ib : Fin d × Bool) :
    LatticeVertex d L :=
  latticeShift ib.1 (signUnit L ib.2) x

/-- **Injectivity of the `2d` neighbour map** (uses `L ≥ 3`).  Two distinct
`(axis, sign)` pairs give distinct neighbours: distinct axes change disjoint
coordinates, and on a common axis `+1 ≠ −1` because `L ≥ 3`. -/
theorem latticeNeighborMap_injective {d L : ℕ} [Fact (2 < L)]
    (x : LatticeVertex d L) :
    Function.Injective (latticeNeighborMap x) := by
  rintro ⟨i, b⟩ ⟨i', b'⟩ h
  unfold latticeNeighborMap at h
  -- Compare the two shifted vertices coordinatewise.
  -- First, the axes must agree: if `i ≠ i'`, evaluate at `i`.
  have hii : i = i' := by
    by_contra hne
    -- At axis `i`, the LHS is `x i + signUnit b`, the RHS is `x i` (axis `i'` ≠ `i`).
    have hL : latticeShift i (signUnit L b) x i = x i + signUnit L b :=
      latticeShift_self i (signUnit L b) x
    have hR : latticeShift i' (signUnit L b') x i = x i :=
      latticeShift_of_ne (signUnit L b') x hne
    have heq : x i + signUnit L b = x i := by rw [← hL, ← hR, h]
    -- `signUnit b = 0` contradicts `±1 ≠ 0` for `L ≥ 3`.
    have h0 : signUnit L b = 0 := by
      have h2 : x i + signUnit L b = x i + 0 := by rw [add_zero]; exact heq
      exact add_left_cancel h2
    rcases signUnit_mem_pm L b with hp | hp
    · rw [hp] at h0; exact one_ne_zero h0
    · rw [hp] at h0
      exact one_ne_zero (by rw [← neg_neg (1 : ZMod L), h0, neg_zero])
  subst hii
  -- Same axis: signs must agree, else `+1 = −1` which fails for `L ≥ 3`.
  have hsign : signUnit L b = signUnit L b' := by
    have := congrFun h i
    rw [latticeShift_self, latticeShift_self] at this
    exact add_left_cancel this
  have hbb : b = b' := by
    -- `b ≠ b'` ⇒ one sign is `1`, the other `-1` ⇒ `1 = -1`, false for `L ≥ 3`.
    cases b <;> cases b'
    · rfl
    · exfalso
      -- `signUnit false = -1`, `signUnit true = 1`: `-1 = 1` is false.
      simp only [signUnit, Bool.false_eq_true, if_false, if_true] at hsign
      exact ZMod.neg_one_ne_one hsign
    · exfalso
      simp only [signUnit, Bool.false_eq_true, if_false, if_true] at hsign
      exact ZMod.neg_one_ne_one hsign.symm
    · rfl
  rw [hbb]

open Classical in
/-- The neighbour finset of `x` is exactly the image of the `2d` shift maps. -/
theorem lattice_neighborFinset_eq_image {d L : ℕ} [Fact (2 < L)]
    (x : LatticeVertex d L) :
    (Finset.univ.filter (fun y => latticeAdjacent x y))
      = Finset.univ.image (latticeNeighborMap x) := by
  classical
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨i, s, hs, rfl⟩
    -- `s = ±1 = signUnit (decide (s = 1))`.
    rcases hs with hs1 | hsm1
    · exact ⟨(i, true), by unfold latticeNeighborMap signUnit; rw [hs1]; simp⟩
    · exact ⟨(i, false), by unfold latticeNeighborMap signUnit; rw [hsm1]; simp⟩
  · rintro ⟨⟨i, b⟩, rfl⟩
    exact ⟨i, signUnit L b, signUnit_mem_pm L b, rfl⟩

/-- **The periodic lattice `Z_L^d` is `2d`-regular** (axiom-clean).  Every vertex
has exactly `2d` neighbours — `2` per axis (`+1`, `−1`), all distinct because
`L ≥ 3` — so the weighted row sum is `2d`. -/
theorem latticeGraph_isRegular (d L : ℕ) [Fact (2 < L)] :
    (latticeGraph d L).isRegular ((2 * d : ℕ) : ℂ) := by
  classical
  intro x
  unfold WeightedGraph.degree
  -- `degree x = ∑ y, [adjacent x y] = #(neighbours) = #(image of 2d shifts) = 2d`.
  have hadj : ∀ y, (latticeGraph d L).adj x y
      = (if latticeAdjacent x y then (1 : ℂ) else 0) := fun _ => rfl
  rw [Finset.sum_congr rfl (fun y _ => hadj y)]
  rw [show (∑ y, (if latticeAdjacent x y then (1 : ℂ) else 0))
        = ((Finset.univ.filter (fun y => latticeAdjacent x y)).card : ℂ) from ?_]
  · rw [lattice_neighborFinset_eq_image x,
      Finset.card_image_of_injective _ (latticeNeighborMap_injective x)]
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    push_cast; ring
  · rw [Finset.card_filter, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : latticeAdjacent x y <;> simp [hy]

/-- **Degree equals `2d`** at any specific vertex (unfolded regularity). -/
theorem latticeGraph_degree (d L : ℕ) [Fact (2 < L)] (x : LatticeVertex d L) :
    (latticeGraph d L).degree x = ((2 * d : ℕ) : ℂ) :=
  latticeGraph_isRegular d L x

/-- **Sparsity / buildability of the lattice: degree is `O(d)`, constant in `N`.**
With `N = L^d` vertices, the lattice degree `2d` is *independent of `N`* for fixed
dimension `d` — bounded, nearest-neighbour coupling, the hallmark of buildable
spatial hardware (optical lattices, superconducting grids, photonic arrays).  This
is exactly why a literal 2D/3D chip is the *most* realizable host.  (Contrast
`K_N`, degree `N − 1`, all-to-all.)  Stated as: the degree `2d` does not depend on
the side length `L` (hence not on `N = L^d`). -/
theorem latticeGraph_sparse (d L L' : ℕ) [Fact (2 < L)] [Fact (2 < L')] :
    (latticeGraph d L).degree (fun _ => 0)
      = (latticeGraph d L').degree (fun _ => 0) := by
  rw [latticeGraph_degree d L, latticeGraph_degree d L']

/-- **The lattice has `N = L^d` vertices.**  Records the vertex count, against
which the constant degree `2d` is the sparsity claim. -/
theorem latticeGraph_card (d L : ℕ) [NeZero L] :
    Fintype.card (LatticeVertex d L) = L ^ d := by
  unfold LatticeVertex
  rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]

/-! ### The marked-vertex lattice search Hamiltonian and distance shells.

The lattice search Hamiltonian is the Childs–Goldstone form
`H = -γ·A(Z_L^d) − |w⟩⟨w|`, identical in shape to the hypercube's — it is just
`(latticeGraph d L).searchHamiltonian {w} γ`.  Unlike the hypercube, the
distance-from-`w` (radial) partition of `Z_L^d` is in general only *almost*
equitable (the `L¹` graph distance shells are not equitable on the torus for
generic `L` because corner/edge wraparound counts break exact branching), which is
itself a symptom of why the spectral analysis is harder; we therefore do *not*
claim an exact equitable radial quotient here.  What is genuine and recorded: the
search Hamiltonian itself, and its entrywise CG form. -/

/-- The **lattice spatial-search Hamiltonian** `H = -γ·A(Z_L^d) − |w⟩⟨w|`, the
Childs–Goldstone marked Hamiltonian on the periodic lattice. -/
noncomputable def latticeSearchHamiltonian (d L : ℕ) [Fact (2 < L)]
    (w : LatticeVertex d L) (γ : ℝ) : Matrix (LatticeVertex d L) (LatticeVertex d L) ℂ :=
  (latticeGraph d L).searchHamiltonian ({w} : Finset (LatticeVertex d L)) γ

/-- Entrywise Childs–Goldstone form of the lattice search Hamiltonian:
`H u v = -γ·[u ∼ v] − [u = v = w]`. -/
theorem latticeSearchHamiltonian_apply (d L : ℕ) [Fact (2 < L)]
    (w : LatticeVertex d L) (γ : ℝ) (u v : LatticeVertex d L) :
    latticeSearchHamiltonian d L w γ u v
      = -(γ : ℂ) * (latticeGraph d L).adj u v
        - (if u = v ∧ u = w then (1 : ℂ) else 0) := by
  unfold latticeSearchHamiltonian WeightedGraph.searchHamiltonian
  simp only [Finset.mem_singleton]

/-! ### The HONEST headline: the dimension threshold.

This is the paper-worthy result, stated precisely with the dimension dependence
explicit.  The proof is the deep Childs–Goldstone spectral integral — genuinely
hard, blocked here. -/

/-- **`lattice_search_dimension_threshold` — the honest headline (Childs–Goldstone,
`quant-ph/0306054`).**  Continuous-time spatial search on the `d`-dimensional
periodic lattice `Z_L^d` achieves the **optimal `Θ(√N)` running time if and only
if `d > 4`**.  Concretely: for `d > 4` the marked-vertex CTQW search is optimal
(`IsOptimalCTQWSearch`); for `d ≤ 4` no choice of coupling `γ` yields the optimal
constant-amplitude `√N` search (`d ≤ 3` fails outright; `d = 4` loses a `√log N`
factor and so still misses the *exact* `Θ(√N)` window).

The mechanism is the infrared convergence of the lattice Green's function
`G_d = (2π)^{-d} ∫_{[-π,π]^d} dᵏ / ∑_{a} (1 − cos kₐ)`, whose small-`k` integrand
`~ ‖k‖^{-2}` is integrable exactly when `d > 4` (a `d/2 > 2` power-counting
threshold) — the same `4`-critical dimension as the random-walk / φ⁴ upper
critical dimension.  Above it, the spectral gap of the normalized search
Hamiltonian is constant (the CNO ratio condition holds) and CG search is optimal;
at and below it the gap closes and the amplitude saturates below `O(1)`.

**Honest `sorry`.**  The spectral integral and its dimension-`4` IR-convergence
threshold are the deep analytic content of Childs–Goldstone; we state the genuine
biconditional and block exactly that step. -/
theorem lattice_search_dimension_threshold (d L : ℕ) [Fact (2 < L)]
    (w : LatticeVertex d L) :
    IsOptimalCTQWSearch (latticeGraph d L) w ↔ 4 < d := by
  -- BLOCKED: Childs–Goldstone spectral integral / d>4 IR-convergence
  -- of the lattice Green's function `∫ dᵏ / ∑(1−cos kₐ)` (quant-ph/0306054).
  sorry

/-- **High-dimensional lattices DO get the speedup (`d > 4`).**  The `d > 4`
half of the threshold: above the critical dimension the lattice Green's function
converges, the CNO spectral-ratio condition holds, and CTQW search is optimal.
(Honest `sorry`, the forward direction of `lattice_search_dimension_threshold`.) -/
theorem lattice_search_optimal_high_dim (d L : ℕ) [Fact (2 < L)]
    (w : LatticeVertex d L) (hd : 4 < d) :
    IsOptimalCTQWSearch (latticeGraph d L) w :=
  (lattice_search_dimension_threshold d L w).mpr hd

/-! ### The honest CONTRAST: buildable vs advantageous are in tension.

This is the conceptual payoff.  A literal 2D/3D lattice is the *most buildable*
quantum search host (constant-degree nearest-neighbour coupling), yet by the
dimension threshold it does **not** get the quadratic search advantage.  The
hypercube `Q_d`, by contrast, has degree `log₂N` (still sub-`N`, still buildable in
the PST/search-chip sense) **and** sits spectrally in the high-dimensional regime,
so it *does* win.  The logarithmic dimensionality of `Q_d` threads the needle
between buildability and advantage that the literal spatial lattice cannot. -/

/-- **`buildable_lattice_structural_contrast` — the axiom-clean structural
contrast.**  The genuinely-proven (axiom-clean) half of the buildability-vs-
advantage tension: the spatial lattice `Z_L^d` is `2d`-regular with `N = L^d`
vertices (constant-degree, maximally buildable), while the Boolean hypercube
`Q_e` is `e`-regular with `e = log₂N` (log-degree, also buildable).  Both
sparsity facts are axiom-clean; this theorem makes **no** dynamical (timing /
advantage) claim — that is `buildable_lattice_dynamical_contrast` (honest-`sorry`). -/
theorem buildable_lattice_structural_contrast
    (d L : ℕ) [Fact (2 < L)] (e : ℕ) :
    -- the lattice is `2d`-regular with `L^d` vertices (proven, axiom-clean):
    ((latticeGraph d L).isRegular ((2 * d : ℕ) : ℂ)
      ∧ Fintype.card (LatticeVertex d L) = L ^ d)
    ∧
    -- the hypercube is `e`-regular with `e = log₂N` (proven, axiom-clean):
    ((Hypercube e).isRegular (e : ℂ)
      ∧ e = Nat.log 2 (Fintype.card (Fin (2 ^ e)))) := by
  exact ⟨⟨latticeGraph_isRegular d L, latticeGraph_card d L⟩,
    ⟨hypercube_isRegular e, hypercube_sparse e⟩⟩

/-- **`buildable_lattice_dynamical_contrast` — the honest dynamical contrast
(`sorry`-carrying).**  For every *physically spatial* lattice — dimension
`d ≤ 3` (every realizable 2D/3D chip), with side `L ≥ 3` — continuous-time
spatial search does **NOT** achieve the optimal `Θ(√N)` quadratic speedup, *even
though the lattice is the most buildable host* (constant degree `2d`,
nearest-neighbour).  Meanwhile the Boolean hypercube `Q_e` (degree `e = log₂N`,
also buildable) **does** achieve it.

Buildability and advantage are therefore in genuine tension: the literal spatial
lattice is maximally buildable but search-suboptimal, while the hypercube's
*logarithmic* dimensionality threads the needle.  Childs–Goldstone
(`quant-ph/0306054`): optimal lattice search requires `d > 4`.

Both dynamical clauses are honestly **unproven**: the lattice non-advantage is
the `d ≤ 3` half of `lattice_search_dimension_threshold` (an honest `sorry`),
and the hypercube advantage is `hypercube_search_optimal_timing` (also an honest
`sorry`).  The axiom-clean structural facts are split off into
`buildable_lattice_structural_contrast`. -/
theorem buildable_lattice_dynamical_contrast
    (d L : ℕ) [Fact (2 < L)] (hd : d ≤ 3) (w : LatticeVertex d L)
    (e : ℕ) (he : 1 ≤ e) (wQ : Fin (2 ^ e)) :
    -- the buildable lattice does NOT get the advantage (d ≤ 3):
    ¬ IsOptimalCTQWSearch (latticeGraph d L) w
    ∧
    -- WHILE the (also buildable, log-degree) hypercube DOES:
    IsOptimalCTQWSearch (Hypercube e) wQ := by
  refine ⟨?_, ?_⟩
  · -- lattice not optimal for d ≤ 3: the negative half of the threshold.
    -- BLOCKED: Childs–Goldstone d ≤ 4 sub-criticality (quant-ph/0306054); for
    -- d ≤ 3 the lattice Green's function diverges in the IR and the search
    -- amplitude saturates below the optimal constant.
    rw [lattice_search_dimension_threshold d L w]
    omega
  · -- hypercube optimal: the honest CNO-timing frontier.
    exact hypercube_search_optimal_timing e he wQ

end SparseSearch
end Graphplay
