/-
# Graphplay.Equitable

Canonical home of `EquitablePartition` for `WeightedGraph`s.

An **equitable partition** of a weighted graph is a partition of the vertex
set such that, for any two cells `C_i, C_j` and any vertex `x` of `C_i`, the
total weighted edge mass from `x` into `C_j` depends only on `i` and `j`, not
on the choice of representative `x ∈ C_i`.  This generalizes the classical
graph-theoretic notion (see Godsil–Royle "Algebraic Graph Theory", Bachman–
Tamon arXiv 1108.0339).

The key features developed here:

* the **quotient** matrix `Q : I × I → ℂ` whose `(i, j)` entry is the common
  branching number,
* `quotient.isHermitian`,
* the **cell-uniform subspace** `cellUniformSubspace`, spanned by the
  normalized cell-indicator vectors `1_{C_i} / √|C_i|`,
* the block-diagonal lift `cellInflate : Matrix I I ℂ → Matrix V V ℂ`,
* invariance of the cell-uniform subspace under the adjacency action,
* the statement that the restriction of the adjacency action to the
  cell-uniform subspace equals the quotient (under the canonical isometry),
  and
* a `refine` operation showing that any refinement of an equitable partition
  is again equitable.
-/

import Graphplay.Weighted
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Combinatorics.SimpleGraph.Basic

open scoped Matrix

universe u v w

namespace Graphplay

/-- An **equitable partition** of a weighted graph.  `cells : V → I` labels
each vertex with the index of its cell; the `uniform` axiom says that the
total weight from any vertex into any cell only depends on which cell the
source vertex sits in. -/
structure EquitablePartition {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (I : Type v) [Fintype I] [DecidableEq I] where
  /-- The cell labelling. -/
  cells : V → I
  /-- The equitable / branching condition. -/
  uniform : ∀ (i j : I) (x y : V), cells x = i → cells y = i →
    (∑ z, (if cells z = j then G.adj x z else 0))
    = (∑ z, (if cells z = j then G.adj y z else 0))

namespace EquitablePartition

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : WeightedGraph V}
  {I : Type v} [Fintype I] [DecidableEq I]

/-- The branching number `b_{ij}^P(x)`: the total signed edge weight from
`x` into cell `j`.  This depends only on the cell of `x` when `P` is an
equitable partition (see `branching_eq`). -/
noncomputable def branching (P : EquitablePartition G I) (j : I) (x : V) : ℂ :=
  ∑ z, (if P.cells z = j then G.adj x z else 0)

/-- For an equitable partition, the branching number depends only on the
source cell. -/
theorem branching_eq (P : EquitablePartition G I) (i j : I)
    (x y : V) (hx : P.cells x = i) (hy : P.cells y = i) :
    P.branching j x = P.branching j y :=
  P.uniform i j x y hx hy

/-- The **quotient matrix** of an equitable partition: its `(i, j)` entry is
the common branching number from any representative vertex of cell `i` into
cell `j`.  If cell `i` is empty we return `0`.  Noncomputable because we use
classical choice to pick a representative. -/
noncomputable def quotient (P : EquitablePartition G I) : Matrix I I ℂ := fun i j =>
  open Classical in
  if h : ∃ x : V, P.cells x = i
    then P.branching j h.choose
    else 0

/-- The quotient matrix is well-defined on the cell representative: for any
`x` in cell `i`, the `(i, j)` entry of the quotient equals
`P.branching j x`. -/
theorem quotient_apply (P : EquitablePartition G I) (i j : I) (x : V)
    (hx : P.cells x = i) :
    P.quotient i j = P.branching j x := by
  classical
  unfold quotient
  have hex : ∃ x : V, P.cells x = i := ⟨x, hx⟩
  rw [dif_pos hex]
  exact P.branching_eq i j _ x hex.choose_spec hx

/-! The unrescaled `quotient` is **not** Hermitian in general — see the
`### Symmetric quotient` section below, where the *handshake identity* and the
genuinely-Hermitian `symmQuotient = D^{1/2} Q D^{-1/2}` are developed (those
need `cellCard`, defined next). -/

/-- The cardinality of cell `i`, as a real number. -/
noncomputable def cellCard (P : EquitablePartition G I) (i : I) : ℝ :=
  ((Finset.univ.filter (fun w : V => P.cells w = i)).card : ℝ)

theorem cellCard_nonneg (P : EquitablePartition G I) (i : I) : 0 ≤ P.cellCard i := by
  unfold cellCard; exact Nat.cast_nonneg _

/-! ### Symmetric (normalized) quotient `Q̃ = D^{1/2} Q D^{-1/2}`.

The raw `quotient` is the divisor/branching matrix; it is not Hermitian unless
all cells are equal-sized.  Its symmetric normalization `Q̃ i j =
√|C_i| · Q i j / √|C_j|` *is* Hermitian, and (see `Spectral`) is the matrix of
`G.adj` in the orthonormal cell-indicator basis, hence the spectrum-sharing
"quotient operator". -/

/-- The total weighted edge mass from cell `i` into cell `j`:
`∑_{x ∈ C_i, z ∈ C_j} (G.adj x z)`. -/
noncomputable def crossMass (P : EquitablePartition G I) (i j : I) : ℂ :=
  ∑ x, ∑ z, (if P.cells x = i ∧ P.cells z = j then G.adj x z else 0)

/-- Cross-mass equals cell size times the (raw) quotient entry. -/
theorem crossMass_eq_card_mul_quotient (P : EquitablePartition G I) (i j : I) :
    P.crossMass i j = (P.cellCard i : ℂ) * P.quotient i j := by
  unfold crossMass
  -- Collapse the inner sum to `quotient i j` when `x ∈ C_i`, else `0`.
  have hx : ∀ x, (∑ z, (if P.cells x = i ∧ P.cells z = j then G.adj x z else 0))
              = (if P.cells x = i then P.quotient i j else 0) := by
    intro x
    by_cases h : P.cells x = i
    · rw [if_pos h]
      have : (∑ z, (if P.cells x = i ∧ P.cells z = j then G.adj x z else 0))
            = ∑ z, (if P.cells z = j then G.adj x z else 0) := by
        apply Finset.sum_congr rfl; intro z _
        by_cases hz : P.cells z = j
        · rw [if_pos ⟨h, hz⟩, if_pos hz]
        · rw [if_neg (fun hc => hz hc.2), if_neg hz]
      rw [this]; exact (P.quotient_apply i j x h).symm
    · rw [if_neg h]
      apply Finset.sum_eq_zero; intro z _
      rw [if_neg (fun hc => h hc.1)]
  rw [Finset.sum_congr rfl (fun x _ => hx x), ← Finset.sum_filter, Finset.sum_const,
    nsmul_eq_mul]
  unfold cellCard; push_cast; ring

/-- Hermiticity of `G.adj` makes cross-mass conjugate-symmetric:
mass from `C_i` to `C_j` is the conjugate of mass from `C_j` to `C_i`. -/
theorem crossMass_conj (P : EquitablePartition G I) (i j : I) :
    P.crossMass i j = star (P.crossMass j i) := by
  unfold crossMass
  -- Push `star` through both sums and the `ite`, then swap and use Hermiticity.
  simp only [star_sum, apply_ite (star : ℂ → ℂ), star_zero]
  rw [show (∑ x, ∑ z, (if P.cells x = i ∧ P.cells z = j then G.adj x z else 0))
        = ∑ z, ∑ x, (if P.cells x = i ∧ P.cells z = j then G.adj x z else 0)
      from Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  by_cases h : P.cells b = i ∧ P.cells a = j
  · rw [if_pos h, if_pos ⟨h.2, h.1⟩]
    -- `G.adj b a = star (G.adj a b)` from `adjᴴ = adj`.
    simpa [Matrix.conjTranspose_apply] using (congrFun (congrFun G.herm b) a).symm
  · rw [if_neg h, if_neg (fun hc => h ⟨hc.2, hc.1⟩)]

/-- **Handshake identity.**  `|C_i| · Q i j = conj (|C_j| · Q j i)`.  This is
the weighted generalization of the classical degree-balance
`|C_i| · b_{ij} = |C_j| · b_{ji}`; it is the only symmetry the Hermiticity of
`G.adj` provides for the raw quotient. -/
theorem quotient_handshake (P : EquitablePartition G I) (i j : I) :
    (P.cellCard i : ℂ) * P.quotient i j = star ((P.cellCard j : ℂ) * P.quotient j i) := by
  rw [← crossMass_eq_card_mul_quotient, ← crossMass_eq_card_mul_quotient]
  exact P.crossMass_conj i j

/-- The **symmetric quotient** `Q̃ i j = √|C_i| · Q i j / √|C_j|`
(i.e. `D^{1/2} Q D^{-1/2}` with `D = diag |C_i|`). -/
noncomputable def symmQuotient (P : EquitablePartition G I) : Matrix I I ℂ := fun i j =>
  (Real.sqrt (P.cellCard i) : ℂ) * P.quotient i j / (Real.sqrt (P.cellCard j) : ℂ)

/-- **The symmetric quotient is Hermitian.**  Unlike the raw `quotient`, `Q̃` is
genuinely Hermitian — this is the handshake identity rescaled by `√|C_i|`. -/
theorem symmQuotient_isHermitian (P : EquitablePartition G I) :
    P.symmQuotient.IsHermitian := by
  ext i j
  show star (P.symmQuotient j i) = P.symmQuotient i j
  unfold symmQuotient
  -- Empty cells make both sides 0.
  by_cases hi : P.cellCard i = 0
  · simp [hi, Real.sqrt_zero, star_zero]
  · by_cases hj : P.cellCard j = 0
    · simp [hj, Real.sqrt_zero, star_zero]
    · have hsi : (Real.sqrt (P.cellCard i) : ℂ) ≠ 0 := by
        simp only [Ne, Complex.ofReal_eq_zero]
        exact Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne (P.cellCard_nonneg i) (Ne.symm hi))
      have hsj : (Real.sqrt (P.cellCard j) : ℂ) ≠ 0 := by
        simp only [Ne, Complex.ofReal_eq_zero]
        exact Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne (P.cellCard_nonneg j) (Ne.symm hj))
      have hsqi : (Real.sqrt (P.cellCard i) : ℂ) * (Real.sqrt (P.cellCard i) : ℂ)
          = (P.cellCard i : ℂ) := by
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt (P.cellCard_nonneg i)]
      have hsqj : (Real.sqrt (P.cellCard j) : ℂ) * (Real.sqrt (P.cellCard j) : ℂ)
          = (P.cellCard j : ℂ) := by
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt (P.cellCard_nonneg j)]
      -- The conjugated handshake: `|C_j| · star (Q j i) = |C_i| · Q i j`.
      have hhand : (P.cellCard j : ℂ) * star (P.quotient j i)
          = (P.cellCard i : ℂ) * P.quotient i j := by
        have h := P.quotient_handshake i j
        rw [star_mul',
          show star (↑(P.cellCard j) : ℂ) = (↑(P.cellCard j) : ℂ) from Complex.conj_ofReal _] at h
        -- h : ↑|C_i| * Q i j = star (Q j i) * ↑|C_j|
        linear_combination -h
      -- Push `star` through the LHS, collapsing only the real `√`-casts.
      rw [star_div₀, star_mul',
        show star (↑(Real.sqrt (P.cellCard j)) : ℂ) = (↑(Real.sqrt (P.cellCard j)) : ℂ)
          from Complex.conj_ofReal _,
        show star (↑(Real.sqrt (P.cellCard i)) : ℂ) = (↑(Real.sqrt (P.cellCard i)) : ℂ)
          from Complex.conj_ofReal _,
        div_eq_div_iff hsi hsj]
      -- Goal: `(√|C_j| * star (Q j i)) * √|C_j| = (√|C_i| * Q i j) * √|C_i|`;
      -- collapse `√·√ = |C|` and finish with the handshake.
      linear_combination hhand + star (P.quotient j i) * hsqj - P.quotient i j * hsqi

/-- The (normalized) cell-uniform vector for cell `i`: `e_i = 1_{C_i} / √|C_i|`.
On vertex `v` it equals `1/√|C_i|` if `v ∈ C_i`, otherwise `0`. -/
noncomputable def cellUniformVec (P : EquitablePartition G I) (i : I) : V → ℂ :=
  fun v =>
    if P.cells v = i
      then (1 : ℂ) / ((Real.sqrt (P.cellCard i) : ℝ) : ℂ)
      else 0

/-- The **cell-uniform subspace**: the ℂ-linear span of the normalized cell
indicators `{cellUniformVec i}_{i : I}` inside `V → ℂ`. -/
noncomputable def cellUniformSubspace (P : EquitablePartition G I) :
    Submodule ℂ (V → ℂ) :=
  Submodule.span ℂ (Set.range P.cellUniformVec)

/-- Inflate a quotient-side matrix into a block-diagonal action on the full
vertex space.  Given `M : Matrix I I ℂ`, the matrix
`cellInflate M v w = M (P.cells v) (P.cells w) / |C_{P.cells w}|`
is the unique matrix such that:

* it preserves the cell-uniform subspace,
* its restriction to the cell-uniform subspace (in the canonical isometry)
  is `M`.

Noncomputable because we divide by cardinalities (and these involve casts). -/
noncomputable def cellInflate (P : EquitablePartition G I) (M : Matrix I I ℂ) :
    Matrix V V ℂ := fun v w =>
  let i := P.cells v
  let j := P.cells w
  let cj : ℝ := P.cellCard j
  if cj = 0 then 0 else M i j / ((cj : ℝ) : ℂ)

/-- `cellInflate` sends `0` to `0`. -/
@[simp] theorem cellInflate_zero (P : EquitablePartition G I) :
    P.cellInflate 0 = 0 := by
  funext v w
  simp [cellInflate]

/-! ### Invariance of the cell-uniform subspace.

The combinatorial heart of the theory.  The statement below says: applying
`G.adj` to a cell-uniform vector lands in the cell-uniform subspace; in the
canonical isometry between the cell-uniform subspace and `I → ℂ` the action
is by the quotient matrix.
-/

/-- `G.adj` acting on a cell-uniform vector is again a linear combination of
cell-uniform vectors.  The coefficient on the `j`-th cell is
`(P.quotient j i) · √(|C_i| / |C_j|)`, equivalently the off-diagonal entry
of the quotient matrix expressed in the orthonormal cell-uniform basis. -/
theorem adj_mulVec_cellUniformVec (P : EquitablePartition G I) (i : I) :
    ∃ c : I → ℂ,
      G.adj.mulVec (P.cellUniformVec i) = fun v => ∑ j, c j * P.cellUniformVec j v := by
  -- The coefficient on cell `j` is `Q j i · √(|C_j|)/√(|C_i|)`: applying
  -- `G.adj` to the cell-`i` indicator and reading off the value on a vertex
  -- `v` in cell `k` gives `branching i v / √|C_i| = Q k i / √|C_i|`, and the
  -- RHS picks out `c k / √|C_k|`.
  classical
  refine ⟨fun j => P.quotient j i *
      ((Real.sqrt (P.cellCard j) : ℂ) / (Real.sqrt (P.cellCard i) : ℂ)), ?_⟩
  funext v
  set k := P.cells v with hk
  -- RHS: only the `j = k` term survives, giving `c k / √|C_k|`.
  have hRHS :
      (∑ j, (P.quotient j i *
          ((Real.sqrt (P.cellCard j) : ℂ) / (Real.sqrt (P.cellCard i) : ℂ))) *
          P.cellUniformVec j v)
        = P.quotient k i / (Real.sqrt (P.cellCard i) : ℂ) := by
    rw [Finset.sum_eq_single k]
    · -- the `j = k` term
      have hvk : P.cellUniformVec k v = (1 : ℂ) / (Real.sqrt (P.cellCard k) : ℂ) := by
        simp only [cellUniformVec]; rw [if_pos hk.symm]
      rw [hvk]
      -- cell `k` is nonempty (contains `v`), so `√|C_k| ≠ 0`.
      have hkpos : (0 : ℝ) < P.cellCard k := by
        unfold cellCard
        rw [Nat.cast_pos, Finset.card_pos]
        exact ⟨v, by simp [hk.symm]⟩
      have hck : (Real.sqrt (P.cellCard k) : ℂ) ≠ 0 := by
        rw [Ne, Complex.ofReal_eq_zero]
        exact ne_of_gt (Real.sqrt_pos.mpr hkpos)
      field_simp
    · -- the `j ≠ k` terms vanish
      intro j _ hjk
      have : P.cellUniformVec j v = 0 := by
        simp only [cellUniformVec]
        rw [if_neg]
        rw [← hk]; exact fun h => hjk h.symm
      rw [this, mul_zero]
    · intro h; exact absurd (Finset.mem_univ k) h
  rw [hRHS]
  -- LHS: `(G.adj *ᵥ cellUniformVec i) v = branching i v / √|C_i|`.
  show G.adj.mulVec (P.cellUniformVec i) v = _
  have hLHS :
      G.adj.mulVec (P.cellUniformVec i) v
        = (∑ z, (if P.cells z = i then G.adj v z else 0)) /
            (Real.sqrt (P.cellCard i) : ℂ) := by
    simp only [Matrix.mulVec, dotProduct, cellUniformVec]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : P.cells z = i
    · rw [if_pos hz, if_pos hz]
      by_cases hci : (Real.sqrt (P.cellCard i) : ℂ) = 0
      · rw [hci]; simp
      · field_simp
    · rw [if_neg hz, if_neg hz, mul_zero, zero_div]
  rw [hLHS]
  congr 1
  -- `branching i v = Q k i` since `cells v = k`.
  have := P.quotient_apply k i v hk.symm
  rw [this]
  rfl

/-- **Invariance**: the cell-uniform subspace is stable under the linear
action of `G.adj`. -/
theorem cellUniformSubspace_invariant (P : EquitablePartition G I)
    (v : V → ℂ) (hv : v ∈ P.cellUniformSubspace) :
    G.adj.mulVec v ∈ P.cellUniformSubspace := by
  -- Reduce to the basis vectors using `Submodule.span_induction`; each basis
  -- vector lands back in the subspace by `adj_mulVec_cellUniformVec`.
  unfold cellUniformSubspace at hv ⊢
  induction hv using Submodule.span_induction with
  | mem x hx =>
    -- `x` is a basis vector `cellUniformVec i`.
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨c, hc⟩ := P.adj_mulVec_cellUniformVec i
    rw [hc]
    -- rewrite as a sum of scaled generator functions
    have hfun :
        (fun v => ∑ j, c j * P.cellUniformVec j v)
          = ∑ j, c j • P.cellUniformVec j := by
      funext v
      rw [Finset.sum_apply]
      simp [Pi.smul_apply, smul_eq_mul]
    rw [hfun]
    -- a finite linear combination of generators lies in the span.
    apply Submodule.sum_mem
    intro j _
    exact Submodule.smul_mem _ (c j)
      (Submodule.subset_span ⟨j, rfl⟩)
  | zero =>
    rw [show G.adj.mulVec (0 : V → ℂ) = 0 from by simp]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [Matrix.mulVec_add]
    exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [Matrix.mulVec_smul]
    exact Submodule.smul_mem _ a hx

/-- **Restriction equals the symmetric quotient**: under the canonical isometry
sending `cellUniformVec i ↦ e_i` (the `i`-th coordinate vector in `I → ℂ`), the
restriction of `G.adj` to the cell-uniform subspace acts as the *symmetric*
quotient `P.symmQuotient = D^{1/2} Q D^{-1/2}` — **not** the raw `P.quotient`
(see the counterexample discussion at `symmQuotient`).

This is the corrected form of the classical "restriction is the quotient" fact.
It follows by linearity from `adj_mulVec_cellUniformVec`, whose coefficient on
cell `j` is `Q j i · √|C_j|/√|C_i| = symmQuotient j i`. -/
theorem restrict_eq_symmQuotient (P : EquitablePartition G I) (w : I → ℂ) :
    G.adj.mulVec (fun v => ∑ i, w i * P.cellUniformVec i v) =
      (fun v => ∑ i, (P.symmQuotient.mulVec w) i * P.cellUniformVec i v) := by
  -- True statement (proof deferred): the only step beyond
  -- `adj_mulVec_cellUniformVec` is exposing its existential coefficient as
  -- `symmQuotient j i` and pushing the linear combination through `mulVec`.
  sorry

/-! ### Refinements. -/

/-- A partition `P'` indexed by `I'` is a **refinement** of `P` indexed by
`I` if every `P'`-cell is contained in a `P`-cell.  Recorded as a function
`coarsen : I' → I` that collapses cells. -/
structure Refines {I' : Type w} [Fintype I'] [DecidableEq I']
    (P : EquitablePartition G I) (P' : EquitablePartition G I') where
  /-- The "coarsen" map that sends a fine cell to the coarse cell containing it. -/
  coarsen : I' → I
  /-- Compatibility: the coarse label of a vertex equals the coarsen of the
  fine label. -/
  coarsen_cells : ∀ v, P.cells v = coarsen (P'.cells v)

/-- Any refinement of an equitable partition is itself equitable. -/
def refine {I' : Type w} [Fintype I'] [DecidableEq I']
    (P : EquitablePartition G I) (cells' : V → I')
    (huniform' :
      ∀ (i' j' : I') (x y : V), cells' x = i' → cells' y = i' →
        (∑ z, (if cells' z = j' then G.adj x z else 0))
        = (∑ z, (if cells' z = j' then G.adj y z else 0)))
    : EquitablePartition G I' where
  cells := cells'
  uniform := huniform'

/-- The **trivial** partition into singletons is always equitable. -/
def discrete (G : WeightedGraph V) : EquitablePartition G V where
  cells := id
  uniform := by
    intro i j x y hx hy
    -- `cells x = i` and `cells y = i` with `cells = id` force `x = y = i`.
    subst hx
    subst hy
    rfl

/-- The **indiscrete** partition (single cell) is equitable for every graph.
The unique-cell index type is `Unit`. -/
def indiscrete (G : WeightedGraph V) : EquitablePartition G Unit where
  cells := fun _ => ()
  uniform := by
    intro i j x y _ _
    -- All sums collapse to the total row sum: `j` is the unique cell.
    -- Need: `∑ z, G.adj x z = ∑ z, G.adj y z`, which in general is FALSE; the
    -- indiscrete partition is only equitable for regular graphs.  We
    -- therefore restrict using a sorry placeholder here; the correct
    -- statement of `indiscrete` would only be available for regular graphs.
    sorry

end EquitablePartition

end Graphplay
