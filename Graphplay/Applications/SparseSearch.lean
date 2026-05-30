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

/-! ## The headline theorem. -/

/-- **`hypercube_sparse_search_advantage` — the headline.**  The Boolean hypercube
`Q_d` is a **degree-`log₂ N` (sparse, physically realizable)** host whose marked
CTQW search dynamics reduce, via its Hamming-distance equitable quotient, to a
`(d+1)`-dimensional search — exhibiting the same quadratic advantage as the
all-to-all `K_n`, but on a buildable graph.

The statement bundles the **genuinely proven (axiom-clean)** halves:

* **Sparsity / buildability.**  `Q_d` is `d`-regular with `d = log₂ N` — log-degree,
  unlike `K_N`'s degree `N − 1`.

* **Equitable reduction.**  The distance-from-`w` partition into the `d+1` cells is
  equitable (the binomial branching), the marked set `{w}` is a union of cells, and
  the host search Hamiltonian collapses to the `(d+1)`-dimensional collapsed-Hamming
  quotient chain (`hypercube_search_quotient_reduction`).

The deep `O(√N)` spectral-gap **timing** clause — that this `(d+1)`-dimensional
reduced search actually reaches constant amplitude in time `O(√N)` — leans on the
CNO spectral-ratio criterion of `Graphplay.Search.CNO`; it is the single honest
`sorry` (the perturbative amplitude/time analysis of arXiv:2004.12686, exactly the
same dynamical core sorried by the `K_n` flagship `complete_graph_optimal_search`). -/
theorem hypercube_sparse_search_advantage (d : ℕ) (hd : 1 ≤ d) (w : Fin (2^d)) :
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
              P'.cellUniformVec ib v))
    ∧
    -- (3) O(√N) TIMING: the reduced search is CNO-optimal (BLOCKED on spectral
    --     timing — the single honest sorry):
    IsOptimalCTQWSearch (Hypercube d) w := by
  refine ⟨⟨hypercube_isRegular d, hypercube_sparse d⟩, ?_, ?_⟩
  · intro γ weights
    exact hypercube_search_quotient_reduction d w γ weights
  · -- BLOCKED: needs CNO spectral-ratio timing
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

end SparseSearch
end Graphplay
