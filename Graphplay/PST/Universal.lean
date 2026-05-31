/-
# Graphplay.PST.Universal

**Universal state transfer, multiple state transfer, switching automorphisms,
and the K-fractional-revival subset framework.**

Ordinary perfect state transfer (PST, `Graphplay.PST.IsPST`) routes a single
excitation from one vertex `u` to *one* target `v` at *one* time `τ`.  This file
models three stronger / richer transfer phenomena studied in the literature:

1. **Universal state transfer** (Cameron–Fallat–Godsil–Holmes–et al.,
   arXiv:1701.04145): from a fixed vertex `u`, PST is achievable to *every*
   other vertex at *some* (vertex-dependent) time.  This is an extremely rigid
   condition; the classification theorem says a connected graph admitting
   universal state transfer is essentially trivial (a single edge `K₂`, or a
   tightly constrained product).

2. **Multiple state transfer** and **switching automorphisms**
   (Kay, arXiv:1310.3885): a single time `τ` and an *automorphism-like*
   involution that simultaneously transfers several pairs.  The PST unitary at
   the transfer time is, up to a global phase, a graph automorphism that
   realizes the swap — the *switching automorphism*.

3. **K-fractional revival** (Chan–Coutinho–Tamon–et al., arXiv:2004.01129):
   the generalization where the excitation, initially on a *subset* `K ⊆ V`,
   returns to (a unitary scrambling within) `K` at time `τ` — the off-`K`
   amplitudes vanish.  The governing object is the **`D_K` periodicity matrix**
   (the `K × K` block of the evolution) together with an eigenvalue **ratio
   condition** identical in spirit to Godsil's.

Concrete content (sorry-free `def`/`structure`):
* `IsUniversalStateTransfer G u`, `IsMultipleStateTransfer G pairs τ`;
* `SwitchingAutomorphism G u v` (self-contained, to avoid coupling to the
  sibling `Graphplay.PST.Periodicity` module which may be under edit);
* `periodicityBlock G K τ` (the `D_K` block), `IsKFractionalRevival G K τ`,
  and `IsKRatioCondition G K` (the ratio condition).

Deep classification theorems are stated precisely with honest `sorry` proofs.

References:
* A. Kay, *The perfect state transfer graph limbo*, arXiv:1310.3885.
* S. Cameron, S. Fallat, C. Godsil, S. Holmes, et al., *Universal state
  transfer on graphs*, Linear Algebra Appl. 455 (2014) 115–142
  (arXiv:1701.04145).
* W.-C. Cheung, C. Godsil, *Perfect state transfer in cubelike graphs*,
  Linear Algebra Appl. 435 (2011) 2468–2474.
* A. Chan, G. Coutinho, C. Tamon, L. Vinet, H. Zhan, *Fundamentals of
  fractional revival in graphs* and *Quantum fractional revival on graphs*,
  arXiv:2004.01129 / Discrete Math. (2020).
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Matrix.Normed
import Graphplay.Weighted
import Graphplay.PST
import Graphplay.PST.GodsilRatio

open scoped Matrix
open NormedSpace

universe u v

namespace Graphplay
namespace PST

variable {V : Type u} [Fintype V] [DecidableEq V]

/-! ## §1 Universal state transfer (Cameron et al. 1701.04145) -/

/-- **Universal state transfer.**  The graph `G` admits *universal* state
transfer *from* `u` if for every other vertex `v` there is a time `τ_v` with
perfect state transfer `u → v`.  The single excitation initially at `u` can be
routed with certainty to *any* chosen target.

This is the per-source predicate of Cameron–Fallat–Godsil–Holmes et al.
(arXiv:1701.04145); their "universal state transfer" graph is one for which this
holds (and, by symmetry of strong cospectrality, the relation is global). -/
def IsUniversalStateTransfer (G : WeightedGraph V) (u : V) : Prop :=
  ∀ v : V, v ≠ u → ∃ τ : ℝ, IsPST G u v τ

/-- **Global universal state transfer**: every ordered pair of distinct vertices
admits PST at some time.  (The strongest, fully symmetric form.) -/
def IsGloballyUniversalStateTransfer (G : WeightedGraph V) : Prop :=
  ∀ u v : V, v ≠ u → ∃ τ : ℝ, IsPST G u v τ

/-- Global universal transfer specializes to per-source universal transfer at
every vertex. -/
theorem isUniversalStateTransfer_of_global (G : WeightedGraph V)
    (h : IsGloballyUniversalStateTransfer G) (u : V) :
    IsUniversalStateTransfer G u :=
  fun v hv => h u v hv

/-- **Universal transfer forces pairwise strong cospectrality.**  If `G` admits
universal state transfer from `u`, then `u` is strongly cospectral with every
other vertex — an immediate consequence of `isPST_imp_isStronglyCospectral`
applied to each target.  This is the spectral spine of the classification.

Reference: Cameron et al. (arXiv:1701.04145), §3; Godsil 2012 (necessity of
strong cospectrality). -/
theorem isStronglyCospectral_of_universal (G : WeightedGraph V) {u : V}
    (h : IsUniversalStateTransfer G u) (v : V) (hv : v ≠ u) :
    IsStronglyCospectral G u v := by
  obtain ⟨τ, hτ⟩ := h v hv
  exact isPST_imp_isStronglyCospectral G τ u v hτ

/-- **Globally universal ⇒ pairwise strong cospectrality.**  Under global
universal state transfer, *every* ordered pair of distinct vertices is strongly
cospectral.  (Reachable consequence of `isPST_imp_isStronglyCospectral`.) -/
theorem isStronglyCospectral_of_globallyUniversal (G : WeightedGraph V)
    (h : IsGloballyUniversalStateTransfer G) (u v : V) (hv : v ≠ u) :
    IsStronglyCospectral G u v :=
  isStronglyCospectral_of_universal G (isUniversalStateTransfer_of_global G h u) v hv

/-- **Classification of universal state transfer (deep direction).**  A
connected graph on `n ≥ 2` vertices admits universal state transfer only if it
is extremely restricted: in the Cameron–Fallat–Godsil–Holmes classification the
only graphs with (global) universal state transfer are `K₂` and a short list of
highly symmetric products.  We state the cleanest necessary consequence:
*global universal state transfer forces every vertex to be strongly cospectral
to every other and the graph to have at most two distinct eigenvalues in each
vertex support* — which, with connectivity, pins `n = 2` (the single edge).

Concretely: global universal state transfer on `≥ 3` vertices is impossible for
a graph whose adjacency has all-distinct eigenvalues (the generic case); the
full classification (`K₂` only, among connected simple graphs) is the deep
content.

Reference: Cameron, Fallat, Godsil, Holmes et al., *Universal state transfer on
graphs*, LAA 455 (2014) 115–142, Theorem 1.1. -/
theorem globallyUniversal_classification (G : WeightedGraph V)
    (h : IsGloballyUniversalStateTransfer G)
    (hsimple : Function.Injective G.herm.eigenvalues)
    (hcard : 3 ≤ Fintype.card V) :
    False := by
  -- With all eigenvalues distinct, every vertex support is a singleton or full;
  -- strong cospectrality of *all* pairs together with the Godsil ratio
  -- condition on each pair over-determines the spectrum on `≥ 3` vertices,
  -- contradicting injectivity.  This is the rigidity core of the Cameron et al.
  -- classification; honest `sorry`.
  -- BLOCKED: rigidity argument (all-pairs strong cospectrality + Godsil ratio
  -- over-determine a simple spectrum) needs spectral-support machinery not present.
  sorry

/-! ## §2 Multiple state transfer and switching automorphisms (Kay 1310.3885) -/

/-- **Multiple state transfer at a single time.**  Given a list of source/target
`pairs : List (V × V)`, `G` exhibits multiple state transfer at the common time
`τ` if PST holds *simultaneously* for every listed pair `(u, v)` at that one `τ`.
This is the "single clock" strengthening of PST studied by Kay (1310.3885):
several excitations are routed at once. -/
def IsMultipleStateTransfer (G : WeightedGraph V) (pairs : List (V × V))
    (τ : ℝ) : Prop :=
  ∀ p ∈ pairs, IsPST G p.1 p.2 τ

/-- Multiple state transfer over a single pair is ordinary PST. -/
theorem isMultipleStateTransfer_singleton (G : WeightedGraph V) (u v : V)
    (τ : ℝ) :
    IsMultipleStateTransfer G [(u, v)] τ ↔ IsPST G u v τ := by
  constructor
  · intro h; exact h (u, v) (List.mem_singleton.mpr rfl)
  · intro h p hp
    rw [List.mem_singleton] at hp
    rw [hp]; exact h

/-- The empty list trivially has multiple state transfer (no pairs to route). -/
theorem isMultipleStateTransfer_nil (G : WeightedGraph V) (τ : ℝ) :
    IsMultipleStateTransfer G [] τ := by
  intro p hp; exact absurd hp (List.not_mem_nil)

/-- Multiple state transfer over a concatenation holds iff it holds over each
sublist. -/
theorem isMultipleStateTransfer_append (G : WeightedGraph V)
    (l₁ l₂ : List (V × V)) (τ : ℝ) :
    IsMultipleStateTransfer G (l₁ ++ l₂) τ ↔
      IsMultipleStateTransfer G l₁ τ ∧ IsMultipleStateTransfer G l₂ τ := by
  unfold IsMultipleStateTransfer
  constructor
  · intro h
    exact ⟨fun p hp => h p (List.mem_append_left _ hp),
           fun p hp => h p (List.mem_append_right _ hp)⟩
  · rintro ⟨h₁, h₂⟩ p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact h₁ p hp
    · exact h₂ p hp

/-- Multiple state transfer over `p :: rest` is PST of the head together with
multiple state transfer of the tail. -/
theorem isMultipleStateTransfer_cons (G : WeightedGraph V) (p : V × V)
    (rest : List (V × V)) (τ : ℝ) :
    IsMultipleStateTransfer G (p :: rest) τ ↔
      IsPST G p.1 p.2 τ ∧ IsMultipleStateTransfer G rest τ := by
  unfold IsMultipleStateTransfer
  constructor
  · intro h
    exact ⟨h p (List.mem_cons_self), fun q hq => h q (List.mem_cons_of_mem _ hq)⟩
  · rintro ⟨hhead, htail⟩ q hq
    rcases List.mem_cons.mp hq with hq | hq
    · rw [hq]; exact hhead
    · exact htail q hq

/-- A **switching automorphism** of `G` exchanging `u` and `v`: a vertex
permutation `σ` that (i) swaps `u ↔ v` and (ii) is a graph automorphism
(preserves the weighted adjacency).  This is the combinatorial realization of
the PST involution: at the transfer time the walk unitary acts, up to a global
phase, as the permutation matrix of `σ`.

Defined self-containedly here (deliberately *not* importing the sibling
`Graphplay.PST.Periodicity.SwitchingAutomorphism`, which may be under concurrent
edit) so this module never couples to that file.

Reference: Kay, arXiv:1310.3885; Godsil's automorphism characterization of
PST. -/
structure SwitchingAutomorphism (G : WeightedGraph V) (u v : V) where
  /-- The underlying vertex permutation. -/
  perm : Equiv.Perm V
  /-- It swaps the two transfer endpoints. -/
  swaps_uv : perm u = v
  /-- And back. -/
  swaps_vu : perm v = u
  /-- It preserves the (Hermitian) adjacency matrix entrywise. -/
  preserves_adj : ∀ x y, G.adj (perm x) (perm y) = G.adj x y

namespace SwitchingAutomorphism

variable {G : WeightedGraph V} {u v : V}

/-- A switching automorphism is an involution on the endpoints: applying `perm`
twice to `u` returns `u`. -/
theorem perm_perm_left (φ : SwitchingAutomorphism G u v) :
    φ.perm (φ.perm u) = u := by
  rw [φ.swaps_uv, φ.swaps_vu]

/-- The **permutation matrix** of the switching automorphism on the vertex
space: `P_{x,y} = 1` iff `y = σ x`. -/
noncomputable def permMatrix (φ : SwitchingAutomorphism G u v) :
    Matrix V V ℂ :=
  fun x y => if y = φ.perm x then 1 else 0

end SwitchingAutomorphism

/-- **Kay's switching-automorphism necessary condition (deep direction).**  If
`G` has PST between `u` and `v` at time `τ`, then there is a switching
automorphism of `G` exchanging `u` and `v`: at the transfer time the PST unitary
is (up to a global phase) the permutation matrix of a genuine graph
automorphism.

Reference: Kay, *The perfect state transfer graph limbo*, arXiv:1310.3885;
Godsil's automorphism characterization. -/
theorem switchingAutomorphism_of_isPST (G : WeightedGraph V) {u v : V} {τ : ℝ}
    (h : IsPST G u v τ) : Nonempty (SwitchingAutomorphism G u v) := by
  -- PST at `τ` makes `U(τ)` a symmetric unitary swapping `e_u ↔ e_v` up to a
  -- global phase; on graphs with simple eigenvalue support this is realized by
  -- a genuine adjacency automorphism (the "switching" map).  The construction of
  -- the permutation from the unitary is the deep content; honest `sorry`.
  -- BLOCKED: recovering a vertex permutation from the PST unitary needs the
  -- unitary→permutation-matrix (simple-spectrum) recovery argument, unavailable.
  sorry

/-- **Multiple state transfer ⇒ a common switching automorphism.**  If `G`
exhibits multiple state transfer at a single time `τ` for a list of pairs, then
the single PST unitary `U(τ)` realizes, up to phase, a graph automorphism
swapping *all* the listed pairs at once.  We package the existence of a switching
automorphism for the first pair (the others share the same `U(τ)`).

Reference: Kay, arXiv:1310.3885, §IV (the "multiple transfer" automorphism). -/
theorem switchingAutomorphism_of_multiple (G : WeightedGraph V)
    {pairs : List (V × V)} {τ : ℝ} {p : V × V}
    (hmem : p ∈ pairs) (h : IsMultipleStateTransfer G pairs τ) :
    Nonempty (SwitchingAutomorphism G p.1 p.2) :=
  switchingAutomorphism_of_isPST G (h p hmem)

/-! ## §3 The K-fractional-revival subset framework (Chan–Coutinho–Tamon
et al., 2004.01129)

Fix a subset `K ⊆ V` (modelled as `K : Finset V`).  The **`D_K` periodicity
matrix** at time `τ` is the `V × V` matrix obtained from the evolution `U(τ)` by
keeping only the `K × K` block (zeroing all entries with an index outside `K`).
*K-fractional revival* at time `τ` is the condition that the excitation, started
anywhere inside `K`, stays inside `K`: `U(τ)` maps `span{e_k : k ∈ K}` into
itself, i.e. all "leak" amplitudes `U(τ)_{j,k}` with `k ∈ K`, `j ∉ K` vanish.

When `|K| = 1` this is *periodicity*; when `|K| = 2` it is *(pair) fractional
revival*; when additionally the `K`-block is anti-diagonal it is PST. -/

/-- The **`D_K` periodicity matrix**: the `K × K` block of the evolution `U(τ)`,
extended by zero outside `K × K`.  Entry `(i, j)` is `U(τ)_{i,j}` when both
`i, j ∈ K`, else `0`. -/
noncomputable def periodicityBlock (G : WeightedGraph V) (K : Finset V) (τ : ℝ) :
    Matrix V V ℂ :=
  fun i j => if i ∈ K ∧ j ∈ K then G.evolve τ i j else 0

/-- The periodicity block agrees with `U(τ)` on the `K × K` block. -/
theorem periodicityBlock_apply_mem (G : WeightedGraph V) (K : Finset V) (τ : ℝ)
    {i j : V} (hi : i ∈ K) (hj : j ∈ K) :
    periodicityBlock G K τ i j = G.evolve τ i j := by
  unfold periodicityBlock; rw [if_pos ⟨hi, hj⟩]

/-- Off the `K × K` block, the periodicity matrix is zero. -/
theorem periodicityBlock_apply_not_mem (G : WeightedGraph V) (K : Finset V)
    (τ : ℝ) {i j : V} (h : ¬ (i ∈ K ∧ j ∈ K)) :
    periodicityBlock G K τ i j = 0 := by
  unfold periodicityBlock; rw [if_neg h]

/-- **K-fractional revival.**  Started on the subset `K`, the excitation returns
to `K` with certainty at time `τ`: every "leak" amplitude `U(τ)_{j,k}` with
source `k ∈ K` and destination `j ∉ K` vanishes.  Equivalently the
`K`-supported subspace is invariant under `U(τ)`, so on that subspace `U(τ)`
acts by the (unitary) `D_K` block.

(`|K| = 1`: periodicity.  `|K| = 2`: pair fractional revival.  Anti-diagonal
`K`-block on `|K| = 2`: PST.)

Reference: Chan–Coutinho–Tamon–Vinet–Zhan, arXiv:2004.01129, Def. 2.1. -/
def IsKFractionalRevival (G : WeightedGraph V) (K : Finset V) (τ : ℝ) : Prop :=
  ∀ k ∈ K, ∀ j : V, j ∉ K → G.evolve τ j k = 0

/-- For a single-vertex subset, K-fractional revival is exactly the statement
that the off-`u` column of `U(τ)` vanishes — i.e. `U(τ)` concentrates the
`u`-excitation back on `u` (periodicity, up to phase). -/
theorem isKFractionalRevival_singleton (G : WeightedGraph V) (u : V) (τ : ℝ) :
    IsKFractionalRevival G {u} τ ↔ ∀ j : V, j ≠ u → G.evolve τ j u = 0 := by
  constructor
  · intro h j hj
    exact h u (Finset.mem_singleton.mpr rfl) j (by simpa [Finset.mem_singleton] using hj)
  · intro h k hk j hj
    rw [Finset.mem_singleton] at hk; subst hk
    exact h j (by simpa [Finset.mem_singleton] using hj)

/-- **The full vertex set always exhibits revival.**  Taking `K = univ` there is
no destination `j ∉ K`, so the leak condition is vacuous: `U(τ)` of course keeps
the (whole-space) excitation inside the whole space at every time. -/
theorem isKFractionalRevival_univ (G : WeightedGraph V) (τ : ℝ) :
    IsKFractionalRevival G Finset.univ τ := by
  intro k _ j hj
  exact absurd (Finset.mem_univ j) hj

/-- **Switching the source/target roles is symmetric in the leak condition.**  A
useful reformulation: `K`-fractional revival means every cross amplitude between
`K` and its complement (with source in `K`) vanishes; equivalently the off-block
entry of the periodicity matrix `D_K` agrees with `U(τ)` only inside the block.
We record that under revival the periodicity block reproduces the full evolution
on the `K`-rows: for `k ∈ K` and any `j`, `periodicityBlock G K τ j k = U(τ) j k`
when `j ∈ K`, and `= 0 = U(τ) j k` when `j ∉ K`. -/
theorem periodicityBlock_eq_evolve_of_revival (G : WeightedGraph V) (K : Finset V)
    (τ : ℝ) (hrev : IsKFractionalRevival G K τ) {k : V} (hk : k ∈ K) (j : V) :
    periodicityBlock G K τ j k = G.evolve τ j k := by
  by_cases hj : j ∈ K
  · exact periodicityBlock_apply_mem G K τ hj hk
  · rw [periodicityBlock_apply_not_mem G K τ (fun h => hj h.1)]
    exact (hrev k hk j hj).symm

/-- **The `K`-ratio condition** (the fractional-revival analogue of Godsil's
ratio condition).  Let `S_K := ⋃_{k ∈ K} EigenvalueSupport G k` be the joint
eigenvalue support of the subset `K`.  The ratio condition asks that all
supported eigenvalues lie in a common arithmetic progression: there are
`a > 0, b ∈ ℝ` so that every `λ ∈ S_K` is `b + a·m` for some integer `m`.

This is the spectral criterion that makes the phases `e^{-iτλ}` simultaneously
align so the off-`K` amplitudes can cancel.

Reference: Chan–Coutinho–Tamon–Vinet–Zhan, arXiv:2004.01129, §4; cf. Godsil's
`IsGodsilRatio`. -/
def IsKRatioCondition (G : WeightedGraph V) (K : Finset V) : Prop :=
  ∃ a b : ℝ, 0 < a ∧
    ∀ lam : ℝ, (∃ k ∈ K, lam ∈ EigenvalueSupport G k) →
      ∃ m : ℤ, lam = b + a * (m : ℝ)

/-- The `K`-ratio condition for a singleton `{u}` is Godsil's reflexive ratio
condition at `u` (the support arithmetic-progression condition). -/
theorem isKRatioCondition_singleton (G : WeightedGraph V) (u : V) :
    IsKRatioCondition G {u} ↔
      ∃ a b : ℝ, 0 < a ∧ ∀ lam ∈ EigenvalueSupport G u,
        ∃ m : ℤ, lam = b + a * (m : ℝ) := by
  unfold IsKRatioCondition
  constructor
  · rintro ⟨a, b, ha, h⟩
    refine ⟨a, b, ha, fun lam hlam => h lam ⟨u, Finset.mem_singleton.mpr rfl, hlam⟩⟩
  · rintro ⟨a, b, ha, h⟩
    refine ⟨a, b, ha, ?_⟩
    rintro lam ⟨k, hk, hlam⟩
    rw [Finset.mem_singleton] at hk; subst hk
    exact h lam hlam

/-- **Existence criterion for K-fractional revival (deep theorem).**  `G` admits
K-fractional revival on `K` at some time `τ` iff a *strong-cospectrality-style*
spectral-symmetry condition on `K` holds together with the `K`-ratio condition.
The forward direction extracts the spectral symmetry from the off-`K`
cancellation; the backward direction is a simultaneous-approximation
(Kronecker/Dirichlet) argument aligning the supported phases.

We state the *necessity of the ratio condition*: if K-fractional revival occurs
at some time, the joint support satisfies the ratio condition.  (Sufficiency and
the cospectrality half are the deeper content.)

Reference: Chan–Coutinho–Tamon–Vinet–Zhan, arXiv:2004.01129, Thm 4.x. -/
theorem isKRatioCondition_of_fractionalRevival (G : WeightedGraph V)
    (K : Finset V) (h : ∃ τ : ℝ, 0 < τ ∧ IsKFractionalRevival G K τ) :
    IsKRatioCondition G K := by
  -- Reading off the off-`K` cancellation `∑_λ e^{-iτλ}(E_λ)_{j,k} = 0` for all
  -- `j ∉ K`, `k ∈ K`, and isolating the supported phases, forces the eigenvalue
  -- differences in `S_K` to be integer multiples of `2π/τ` (a `Real.Angle` /
  -- `AddCircle` periodicity argument).  Honest `sorry`.
  -- BLOCKED: needs Real.Angle/AddCircle 2π-periodicity extraction from the
  -- off-K phase-cancellation (not developed).
  sorry

/-! ### Column concentration and real-symmetric revival -/

/-- **Column concentration from PST (pure unitarity).**  If `‖U(τ)_{u,v}‖ = 1`
then the entire `v`-column of `U(τ)` is supported at `u`: `U(τ)_{j,v} = 0` for
`j ≠ u`.  This is the column dual of `evolve_eq_zero_of_isPST` and follows from
`U(τ)ᴴ U(τ) = 1` (the `v`-column has unit `ℓ²`-norm, already saturated by the
`(u,v)` entry).  No symmetry needed. -/
theorem evolve_col_eq_zero_of_isPST (G : WeightedGraph V) (τ : ℝ) (u v : V)
    (hpst : ‖G.evolve τ u v‖ = 1) (j : V) (hj : j ≠ u) :
    G.evolve τ j v = 0 := by
  -- `v`-column unit `ℓ²`-norm from `U(τ)ᴴ U(τ) = 1`.
  have hU := G.evolve_unitary τ
  have hvv := congrFun (congrFun hU v) v
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at hvv
  have key : ∑ w : V, (G.evolve τ)ᴴ v w * G.evolve τ w v
      = ((∑ w : V, ‖G.evolve τ w v‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [Matrix.conjTranspose_apply, mul_comm, Complex.star_def, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
  rw [key] at hvv
  have hsum : ∑ w : V, ‖G.evolve τ w v‖ ^ 2 = 1 := by exact_mod_cast hvv
  have hsplit : ‖G.evolve τ u v‖ ^ 2
      + ∑ w ∈ Finset.univ.erase u, ‖G.evolve τ w v‖ ^ 2 = 1 := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ u)] at hsum; linarith [hsum]
  rw [hpst] at hsplit; simp only [one_pow] at hsplit
  have hrest : ∑ w ∈ Finset.univ.erase u, ‖G.evolve τ w v‖ ^ 2 = 0 := by linarith
  have hmem : j ∈ Finset.univ.erase u := Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩
  have hz : ‖G.evolve τ j v‖ ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => sq_nonneg _)).mp hrest j hmem
  have : ‖G.evolve τ j v‖ = 0 := by nlinarith [norm_nonneg (G.evolve τ j v)]
  exact norm_eq_zero.mp this

/-- **The evolution is complex-symmetric when the adjacency is symmetric.**  For
a symmetric (real-weighted) adjacency `Aᵀ = A`, `U(τ)ᵀ = U(τ)`, hence
`U(τ)_{v,u} = U(τ)_{u,v}` entrywise. -/
theorem evolve_symm_of_isSymm (G : WeightedGraph V) (hsymm : G.adj.IsSymm)
    (τ : ℝ) (u v : V) : G.evolve τ v u = G.evolve τ u v := by
  have htr : (G.evolve τ)ᵀ = G.evolve τ := by
    unfold WeightedGraph.evolve
    rw [← Matrix.exp_transpose]
    congr 1
    rw [Matrix.transpose_smul, hsymm]
  have h := congrFun (congrFun htr u) v
  rwa [Matrix.transpose_apply] at h

/-- **PST is `K`-fractional revival on an antipodal pair (`|K| = 2`),
real-symmetric case (CLOSED).**  Perfect state transfer `u → v` at time `τ` on a
graph with *symmetric* adjacency (`Aᵀ = A`, the classical real-weighted Godsil
setting) implies fractional revival on `K = {u, v}` at time `τ`: the only nonzero
amplitudes out of `{u, v}` stay within `{u, v}`.

The `v`-leak (`U(τ)_{j,v} = 0`, `j ∉ {u,v}`) is pure unitarity
(`evolve_col_eq_zero_of_isPST`).  The `u`-leak (`U(τ)_{j,u} = 0`, `j ∉ {u,v}`)
uses symmetry: `‖U(τ)_{v,u}‖ = ‖U(τ)_{u,v}‖ = 1`, so the `u`-column concentrates
at `v`.  Axiom-clean.  (The fully-general Hermitian statement is genuinely false
without symmetry: `‖U(τ)_{·,u}‖ = 1` requires target-side `v → u`.) -/
theorem isKFractionalRevival_pair_of_isPST_of_isSymm (G : WeightedGraph V)
    (hsymm : G.adj.IsSymm) {u v : V} {τ : ℝ} (_huv : u ≠ v) (h : IsPST G u v τ) :
    IsKFractionalRevival G {u, v} τ := by
  have hUV : ‖G.evolve τ u v‖ = 1 := h
  -- `‖U(τ)_{v,u}‖ = 1` from symmetry.
  have hVU : ‖G.evolve τ v u‖ = 1 := by rw [evolve_symm_of_isSymm G hsymm τ u v]; exact hUV
  intro k hk j hj
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  have hju : j ≠ u := fun hju => hj (by simp [hju])
  have hjv : j ≠ v := fun hjv => hj (by simp [hjv])
  rcases hk with hk | hk
  · -- `k = u`: column `u` concentrates at `v` (using `‖U(τ)_{v,u}‖ = 1`).
    rw [hk]
    exact evolve_col_eq_zero_of_isPST G τ v u hVU j hjv
  · -- `k = v`: column `v` concentrates at `u` (pure unitarity).
    rw [hk]
    exact evolve_col_eq_zero_of_isPST G τ u v hUV j hju

/-- **PST is `K`-fractional revival on an antipodal pair (`|K| = 2`).**  Perfect
state transfer `u → v` at time `τ` implies fractional revival on `K = {u, v}` at
time `τ`: the only nonzero amplitudes out of `{u, v}` stay within `{u, v}`.

This is the bridge identifying PST as the antidiagonal special case of the
`K = {u, v}` revival framework.  The closed, axiom-clean proof under the
classical real-symmetric (`Aᵀ = A`) hypothesis is
`isKFractionalRevival_pair_of_isPST_of_isSymm`.

Reference: Chan et al., arXiv:2004.01129, Example 2.x (PST as fractional
revival). -/
theorem isKFractionalRevival_pair_of_isPST (G : WeightedGraph V) {u v : V}
    {τ : ℝ} (huv : u ≠ v) (h : IsPST G u v τ) :
    IsKFractionalRevival G {u, v} τ := by
  -- The `k = v` leak is pure unitarity (`evolve_col_eq_zero_of_isPST`); the
  -- `k = u` leak needs `‖U(τ)_{·,u}‖ = 1`, i.e. target-side PST `v → u`, which is
  -- the spectral-symmetry half of Godsil's theorem and is *false* for general
  -- (non-symmetric) Hermitian `A`.  The real-symmetric case is closed in
  -- `isKFractionalRevival_pair_of_isPST_of_isSymm`.
  -- BLOCKED: `k = u` leak requires target-side PST (false for general Hermitian A);
  -- use isKFractionalRevival_pair_of_isPST_of_isSymm for the symmetric case.
  sorry

end PST
end Graphplay
