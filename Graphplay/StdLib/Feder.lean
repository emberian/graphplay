/-
# Graphplay.StdLib.Feder

**The Feder bosonic / fermionic many-particle quantum-walk family.**

Feder's construction (D. M. Feder, *Phys. Rev. Lett.* **97**, 180502 (2006),
"Perfect quantum state transfer with bosons") realises perfect state transfer
(PST) of `k` indistinguishable particles hopping on a host graph `G`.  The
many-particle dynamics live on a *configuration space*; for `k` walkers the
configurations are either:

* **boson** configurations — `k`-element *multisets* of vertices, equivalently
  (since the second-quantised hopping is symmetric) the symmetric quotient of
  `k`-tuples `Fin k → V`; the `k`-particle adjacency is the **symmetric power**
  `G^{⊙k}`; or
* **fermion** configurations — `k`-element *subsets* `Finset V` of size `k`
  (Pauli exclusion: at most one particle per vertex); the `k`-particle
  adjacency is the **exterior power** `⋀ᵏ G`, whose hop amplitude carries the
  Jordan–Wigner / permutation **sign**.

The references for the exterior-power (fermionic) family are Ge, Greenberg,
Perez–Tamon, "Perfect state transfer, graph products, and equitable
partitions" (arXiv:1009.1340) and the exterior-power treatment of
arXiv:1301.0973.  The single-particle PST of `G` lifts to the whole
`k`-particle family — this is **Feder's theorem**.

This file is a *clean standalone* model built directly on
`Graphplay.Weighted`.  We take the configuration space to be the **tuple
space** `Fin k → V` (which carries free `Fintype`/`DecidableEq` instances), and
realise the boson / fermion statistics at the level of the **hop matrix**:

* the *hop relation* `OneMove x y` holds when the two tuples differ in exactly
  one coordinate, by an edge of `G` (a single particle moves along an edge);
* the **symmetric (bosonic)** adjacency sums the host amplitude over the moving
  coordinate;
* the **antisymmetric (fermionic)** adjacency multiplies by the permutation
  sign of the transposition that realises the move (Jordan–Wigner string).

We prove `herm` and `loopless` for both as genuine `WeightedGraph`s.  The
single-particle-to-`k`-particle PST lift (Feder's theorem) and the
symmetric/antisymmetric subspace projection are stated precisely with honest
`sorry` on the deep bodies.

References:

  * D. M. Feder, "Perfect quantum state transfer with bosons",
    *Phys. Rev. Lett.* **97**, 180502 (2006).
  * Ge, Greenberg, Perez, Tamon, "Perfect state transfer, graph products and
    equitable partitions" (arXiv:1009.1340).
  * exterior-power / fermionic PST (arXiv:1301.0973).
  * Bachman, Tamon et al., "Perfect state transfer on quotient graphs"
    (arXiv:1108.0339).
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.GroupTheory.Perm.Sign
import Graphplay.Weighted
import Graphplay.PST

open scoped Matrix
open NormedSpace

universe u

namespace Graphplay

namespace Feder

variable {V : Type u} [Fintype V] [DecidableEq V]

/-! ## 1.  The `k`-particle configuration space and the single-move relation -/

/-- The **`k`-particle (tuple) configuration space**: an ordered `k`-tuple of
vertices.  The bosonic and fermionic walks are obtained by (anti)symmetrising
the hop matrix on this space; the tuple space carries free `Fintype` and
`DecidableEq` instances, which keeps the matrix algebra (and hence the
continuous-time walk `exp(-iτH)`) entirely concrete. -/
abbrev Config (V : Type u) (k : ℕ) : Type u := Fin k → V

/-- The set of coordinates at which two configurations differ. -/
def diffSet (x y : Config V k) : Finset (Fin k) :=
  Finset.univ.filter (fun i => x i ≠ y i)

/-- A **single move**: `x` and `y` agree on all coordinates except exactly one,
say `i`, at which `x i` and `y i` are joined by an edge of `G` (the host
amplitude `G.adj (x i) (y i)` is the move weight, generically nonzero).  This
is the elementary one-particle hop in the `k`-particle walk. -/
def OneMove (G : WeightedGraph V) (x y : Config V k) (i : Fin k) : Prop :=
  (∀ j, j ≠ i → x j = y j) ∧ x i ≠ y i

instance (G : WeightedGraph V) (x y : Config V k) (i : Fin k) :
    Decidable (OneMove G x y i) := by
  unfold OneMove; infer_instance

/-- The host hop amplitude carried by a single move at coordinate `i`:
`G.adj (x i) (y i)`. -/
noncomputable def moveAmpl (G : WeightedGraph V) (x y : Config V k) (i : Fin k) : ℂ :=
  G.adj (x i) (y i)

/-! ## 2.  The bosonic (symmetric-power) `k`-particle adjacency -/

/-- The **bosonic `k`-particle adjacency matrix** `G^{⊙k}` on the tuple
configuration space.  The matrix element between configurations `x` and `y` is
the sum, over coordinates `i` realising a single move `x →ᵢ y`, of the host
amplitude `G.adj (x i) (y i)`.  Symmetric power: no sign, the bosonic hop simply
adds amplitudes across the moving particle.

(For tuples differing in `≥ 2` coordinates the element is `0`; the diagonal is
`0` by looplessness — a hop must change at least one coordinate.) -/
noncomputable def bosonicAdj (G : WeightedGraph V) (k : ℕ) :
    Matrix (Config V k) (Config V k) ℂ :=
  fun x y => ∑ i : Fin k, if OneMove G x y i then moveAmpl G x y i else 0

/-- **Bosonic `k`-particle adjacency is Hermitian.**  A single move `x →ᵢ y`
is reversed by the single move `y →ᵢ x` at the same coordinate, and the host
amplitude is conjugate-symmetric (`star (G.adj a b) = G.adj b a`). -/
theorem bosonicAdj_isHermitian (G : WeightedGraph V) (k : ℕ) :
    (bosonicAdj G k).IsHermitian := by
  refine Matrix.IsHermitian.ext ?_
  intro x y
  show star (bosonicAdj G k y x) = bosonicAdj G k x y
  unfold bosonicAdj moveAmpl
  rw [star_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases h : OneMove G y x i
  · have h' : OneMove G x y i :=
      ⟨fun j hj => (h.1 j hj).symm, fun hc => h.2 hc.symm⟩
    rw [if_pos h, if_pos h']
    exact G.herm.apply (x i) (y i)
  · have h' : ¬ OneMove G x y i := by
      intro hc; exact h ⟨fun j hj => (hc.1 j hj).symm, fun he => hc.2 he.symm⟩
    rw [if_neg h, if_neg h', star_zero]

/-- The bosonic `k`-particle adjacency is **loopless**: the diagonal vanishes,
because a single move requires `x i ≠ y i` at the moving coordinate, which is
impossible when `y = x`. -/
theorem bosonicAdj_loopless (G : WeightedGraph V) (k : ℕ) (x : Config V k) :
    bosonicAdj G k x x = 0 := by
  unfold bosonicAdj
  refine Finset.sum_eq_zero (fun i _ => ?_)
  have : ¬ OneMove G x x i := fun h => h.2 rfl
  rw [if_neg this]

/-- The **bosonic `k`-particle Feder walk** `G^{⊙k}` packaged as a
`WeightedGraph` on the tuple configuration space. -/
noncomputable def bosonicWalk (G : WeightedGraph V) (k : ℕ) :
    WeightedGraph (Config V k) where
  adj := bosonicAdj G k
  herm := bosonicAdj_isHermitian G k
  loopless := bosonicAdj_loopless G k

/-! ## 3.  The fermionic (exterior-power) `k`-particle adjacency

The fermionic walk lives on the same tuple space but the hop carries the
**Jordan–Wigner / permutation sign**.  For a single move at coordinate `i` the
sign is `(-1)` raised to the number of *other* particles sitting (in the fixed
linear `Fin k` order) strictly between the source and destination — equivalently
the sign of the cyclic shift that re-sorts the moved particle back into order.

We record the sign abstractly as the sign of a fixed permutation attached to
the move; concretely, for the standard fermionic walk on `Fin k → V` the sign
is `signOfMove`, defined as the parity of the count of coordinates whose vertex
label lies strictly between `x i` and `y i` in the fixed vertex order. -/

/-- The canonical linear index of a vertex, using the choice-fixed
`Fintype.equivFin` ordering on `V`.  Pins down the site order for the
Jordan–Wigner string. -/
noncomputable def siteIndex (w : V) : ℕ := ((Fintype.equivFin V) w).val

/-- The Jordan–Wigner **sign** of a single move at coordinate `i`: `(-1)` to the
number of coordinates `j ≠ i` whose vertex `x j` (`= y j`, since they agree off
`i`) has a `siteIndex` strictly between those of `x i` and `y i` in the fixed
vertex order.  These are exactly the occupied modes the moved fermion must
anticommute past.  This is symmetric in `(x i, y i)` (the open interval between
two endpoints is the same in either direction), which is what makes the
fermionic adjacency Hermitian once combined with `G.herm`. -/
noncomputable def signOfMove (x y : Config V k) (i : Fin k) : ℤ :=
  (-1 : ℤ) ^ (Finset.univ.filter (fun j : Fin k =>
      j ≠ i ∧
      min (siteIndex (x i)) (siteIndex (y i)) < siteIndex (x j) ∧
      siteIndex (x j) < max (siteIndex (x i)) (siteIndex (y i)))).card

/-- The fermionic sign is invariant under swapping the move endpoints: the open
interval `(min, max)` and the side-condition `j ≠ i` are symmetric in
`x i ↔ y i`, and on a single move `x j = y j` for all `j ≠ i`, so the counted
set is literally the same. -/
theorem signOfMove_symm (G : WeightedGraph V) {x y : Config V k} {i : Fin k}
    (hxy : OneMove G x y i) :
    signOfMove x y i = signOfMove y x i := by
  unfold signOfMove
  congr 2
  refine Finset.filter_congr (fun j _ => ?_)
  by_cases hj : j = i
  · subst hj; simp
  · -- `x j = y j` off the moving coordinate, and `min`/`max` are symmetric.
    have hxj : x j = y j := hxy.1 j hj
    rw [hxj, min_comm (siteIndex (x i)) (siteIndex (y i)),
        max_comm (siteIndex (x i)) (siteIndex (y i))]

/-- The **fermionic `k`-particle adjacency matrix** `⋀ᵏ G` on the tuple
configuration space.  The matrix element between `x` and `y` is the sum over
single-move coordinates `i` of the **signed** host amplitude
`signOfMove x y i · G.adj (x i) (y i)`.  Exterior power: the Jordan–Wigner sign
makes the wavefunction antisymmetric under exchange. -/
noncomputable def fermionicAdj (G : WeightedGraph V) (k : ℕ) :
    Matrix (Config V k) (Config V k) ℂ :=
  fun x y => ∑ i : Fin k,
    if OneMove G x y i then (signOfMove x y i : ℂ) * moveAmpl G x y i else 0

/-- **Fermionic `k`-particle adjacency is Hermitian.**  The reverse move
`y →ᵢ x` carries the same Jordan–Wigner sign (`signOfMove_symm`) — the sign is a
real `±1` so it is its own conjugate — and the host amplitude is
conjugate-symmetric, so the `(x, y)` and conjugated `(y, x)` entries agree. -/
theorem fermionicAdj_isHermitian (G : WeightedGraph V) (k : ℕ) :
    (fermionicAdj G k).IsHermitian := by
  refine Matrix.IsHermitian.ext ?_
  intro x y
  show star (fermionicAdj G k y x) = fermionicAdj G k x y
  unfold fermionicAdj moveAmpl
  rw [star_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases h : OneMove G y x i
  · have h' : OneMove G x y i :=
      ⟨fun j hj => (h.1 j hj).symm, fun hc => h.2 hc.symm⟩
    rw [if_pos h, if_pos h']
    -- `star ((-1)^k * G.adj (y i) (x i)) = (-1)^k * G.adj (x i) (y i)`.
    rw [star_mul']
    have hsign : star ((signOfMove y x i : ℂ)) = (signOfMove x y i : ℂ) := by
      rw [signOfMove_symm G h]
      -- an integer cast is self-conjugate
      rw [star_intCast]
    rw [hsign, G.herm.apply (x i) (y i), mul_comm]
  · have h' : ¬ OneMove G x y i := by
      intro hc; exact h ⟨fun j hj => (hc.1 j hj).symm, fun he => hc.2 he.symm⟩
    rw [if_neg h, if_neg h', star_zero]

/-- The fermionic `k`-particle adjacency is **loopless**: a single move needs
`x i ≠ y i`, impossible on the diagonal. -/
theorem fermionicAdj_loopless (G : WeightedGraph V) (k : ℕ) (x : Config V k) :
    fermionicAdj G k x x = 0 := by
  unfold fermionicAdj
  refine Finset.sum_eq_zero (fun i _ => ?_)
  have : ¬ OneMove G x x i := fun h => h.2 rfl
  rw [if_neg this]

/-- The **fermionic `k`-particle Feder walk** `⋀ᵏ G` packaged as a
`WeightedGraph` on the tuple configuration space. -/
noncomputable def fermionicWalk (G : WeightedGraph V) (k : ℕ) :
    WeightedGraph (Config V k) where
  adj := fermionicAdj G k
  herm := fermionicAdj_isHermitian G k
  loopless := fermionicAdj_loopless G k

/-! ## 4.  Symmetric / antisymmetric subspaces and the Feder lift -/

/-- The diagonal action of `Equiv.Perm (Fin k)` on configurations: `(π · x) =
x ∘ π`.  Relabelling the particles. -/
def permConfig (π : Equiv.Perm (Fin k)) (x : Config V k) : Config V k :=
  fun i => x (π i)

/-- A configuration wavefunction `ψ : Config V k → ℂ` is **symmetric** (bosonic)
if it is invariant under every particle relabelling. -/
def IsSymmetric (k : ℕ) (ψ : Config V k → ℂ) : Prop :=
  ∀ (π : Equiv.Perm (Fin k)) (x : Config V k), ψ (permConfig π x) = ψ x

/-- A configuration wavefunction `ψ : Config V k → ℂ` is **antisymmetric**
(fermionic) if relabelling by `π` multiplies it by `Equiv.Perm.sign π`. -/
def IsAntisymmetric (k : ℕ) (ψ : Config V k → ℂ) : Prop :=
  ∀ (π : Equiv.Perm (Fin k)) (x : Config V k),
    ψ (permConfig π x) = (Equiv.Perm.sign π : ℂ) * ψ x

/-- `permConfig` is a (left-)action up to the group multiplication on `Perm`:
`permConfig π (permConfig σ x) = permConfig (σ * π) x`. -/
theorem permConfig_permConfig (π σ : Equiv.Perm (Fin k)) (x : Config V k) :
    permConfig π (permConfig σ x) = permConfig (σ * π) x := by
  funext i; rfl

/-- `permConfig π` as an equivalence on the configuration space, with inverse
`permConfig π⁻¹`.  This is the reindexing bijection of the matrix-vector sum. -/
def permConfigEquiv (π : Equiv.Perm (Fin k)) : Config V k ≃ Config V k where
  toFun := permConfig π
  invFun := permConfig π⁻¹
  left_inv x := by
    rw [permConfig_permConfig, mul_inv_cancel]; rfl
  right_inv x := by
    rw [permConfig_permConfig, inv_mul_cancel]; rfl

/-- **`OneMove` is `permConfig`-equivariant.**  Relabelling both configurations
by `π` carries the move at coordinate `π i` to the move at coordinate `i`. -/
theorem oneMove_permConfig (G : WeightedGraph V) (π : Equiv.Perm (Fin k))
    (x y : Config V k) (i : Fin k) :
    OneMove G (permConfig π x) (permConfig π y) i ↔ OneMove G x y (π i) := by
  unfold OneMove permConfig
  constructor
  · rintro ⟨hagree, hne⟩
    refine ⟨fun j hj => ?_, hne⟩
    -- write `j = π (π⁻¹ j)`, with `π⁻¹ j ≠ i`
    have : π⁻¹ j ≠ i := fun e => hj (by rw [← e]; simp)
    have hh := hagree (π⁻¹ j) this
    have he : π (π⁻¹ j) = j := by simp
    rwa [he] at hh
  · rintro ⟨hagree, hne⟩
    refine ⟨fun j hj => hagree (π j) (fun e => hj (π.injective e)), hne⟩

/-- **The bosonic adjacency is `permConfig`-equivariant.**
`bosonicAdj G k (permConfig π x) (permConfig π y) = bosonicAdj G k x y`. -/
theorem bosonicAdj_permConfig (G : WeightedGraph V) (k : ℕ)
    (π : Equiv.Perm (Fin k)) (x y : Config V k) :
    bosonicAdj G k (permConfig π x) (permConfig π y) = bosonicAdj G k x y := by
  unfold bosonicAdj moveAmpl
  rw [← Equiv.sum_comp π (fun i => if OneMove G x y i then G.adj (x i) (y i) else 0)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  show (if OneMove G (permConfig π x) (permConfig π y) i
          then G.adj ((permConfig π x) i) ((permConfig π y) i) else 0)
      = (if OneMove G x y (π i) then G.adj (x (π i)) (y (π i)) else 0)
  rw [if_congr (oneMove_permConfig G π x y i) rfl rfl]
  rfl

/-- **The bosonic walk preserves the symmetric subspace.**  If `ψ` is symmetric
then so is `(bosonicAdj G k) *ᵥ ψ`: the symmetric power acts within the bosonic
sector.  This is the projection statement underlying Feder's reduction to the
symmetric-power host. -/
theorem bosonic_preserves_symmetric (G : WeightedGraph V) (k : ℕ)
    (ψ : Config V k → ℂ) (hψ : IsSymmetric k ψ) :
    IsSymmetric k ((bosonicAdj G k).mulVec ψ) := by
  intro π x
  -- The hop matrix is `permConfig`-equivariant and `ψ` is invariant, so the
  -- matrix-vector product is again invariant after reindexing the sum by `π`.
  simp only [Matrix.mulVec, dotProduct]
  rw [← (permConfigEquiv π).sum_comp
    (fun y => bosonicAdj G k (permConfig π x) y * ψ y)]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  show bosonicAdj G k (permConfig π x) (permConfig π y) * ψ (permConfig π y)
      = bosonicAdj G k x y * ψ y
  rw [bosonicAdj_permConfig G k π x y, hψ π y]

/-- **The Jordan–Wigner sign is `permConfig`-equivariant.**  Relabelling both
configurations by `π` carries the sign at coordinate `i` to the sign at
coordinate `π i`: the counted set of intervening occupied modes is reindexed by
`π` but its cardinality is unchanged. -/
theorem signOfMove_permConfig (π : Equiv.Perm (Fin k)) (x y : Config V k)
    (i : Fin k) :
    signOfMove (permConfig π x) (permConfig π y) i = signOfMove x y (π i) := by
  unfold signOfMove permConfig
  -- It suffices that the two counted finsets have equal cardinality.
  suffices h : (Finset.univ.filter (fun j : Fin k =>
      j ≠ i ∧
      min (siteIndex (x (π i))) (siteIndex (y (π i))) < siteIndex (x (π j)) ∧
      siteIndex (x (π j)) < max (siteIndex (x (π i))) (siteIndex (y (π i))))).card
    = (Finset.univ.filter (fun j : Fin k =>
      j ≠ π i ∧
      min (siteIndex (x (π i))) (siteIndex (y (π i))) < siteIndex (x j) ∧
      siteIndex (x j) < max (siteIndex (x (π i))) (siteIndex (y (π i))))).card by
    rw [h]
  -- Reindex by the bijection `j ↦ π j`.
  refine Finset.card_nbij' (fun j => π j) (fun j => π⁻¹ j) ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hj ⊢
    exact ⟨fun e => hj.1 (π.injective e), hj.2.1, hj.2.2⟩
  · intro j hj
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hj ⊢
    have he : π (π⁻¹ j) = j := by simp
    refine ⟨fun e => hj.1 (by rw [← e]; simp), ?_, ?_⟩
    · rw [he]; exact hj.2.1
    · rw [he]; exact hj.2.2
  · intro j _; simp
  · intro j _; simp

/-- **The fermionic adjacency is `permConfig`-equivariant.**
`fermionicAdj G k (permConfig π x) (permConfig π y) = fermionicAdj G k x y`. -/
theorem fermionicAdj_permConfig (G : WeightedGraph V) (k : ℕ)
    (π : Equiv.Perm (Fin k)) (x y : Config V k) :
    fermionicAdj G k (permConfig π x) (permConfig π y) = fermionicAdj G k x y := by
  unfold fermionicAdj moveAmpl
  rw [← Equiv.sum_comp π
    (fun i => if OneMove G x y i then (signOfMove x y i : ℂ) * G.adj (x i) (y i) else 0)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  show (if OneMove G (permConfig π x) (permConfig π y) i
          then (signOfMove (permConfig π x) (permConfig π y) i : ℂ)
                * G.adj ((permConfig π x) i) ((permConfig π y) i) else 0)
      = (if OneMove G x y (π i) then (signOfMove x y (π i) : ℂ)
                * G.adj (x (π i)) (y (π i)) else 0)
  rw [if_congr (oneMove_permConfig G π x y i) rfl rfl, signOfMove_permConfig π x y i]
  rfl

/-- **The fermionic walk preserves the antisymmetric subspace.**  If `ψ` is
antisymmetric then so is `(fermionicAdj G k) *ᵥ ψ`: the exterior power acts
within the fermionic sector. -/
theorem fermionic_preserves_antisymmetric (G : WeightedGraph V) (k : ℕ)
    (ψ : Config V k → ℂ) (hψ : IsAntisymmetric k ψ) :
    IsAntisymmetric k ((fermionicAdj G k).mulVec ψ) := by
  intro π x
  simp only [Matrix.mulVec, dotProduct]
  rw [← (permConfigEquiv π).sum_comp
    (fun y => fermionicAdj G k (permConfig π x) y * ψ y), Finset.mul_sum]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  show fermionicAdj G k (permConfig π x) (permConfig π y) * ψ (permConfig π y)
      = (Equiv.Perm.sign π : ℂ) * (fermionicAdj G k x y * ψ y)
  rw [fermionicAdj_permConfig G k π x y, hψ π y]
  ring

/-- The **`k`-fold "diagonal" configuration** `diagConfig v = (v, v, …, v)`:
all `k` particles on the same vertex `v`.  Used to state single-particle PST
lifting (the `k`-boson state where every particle starts at `u`). -/
def diagConfig (k : ℕ) (v : V) : Config V k := fun _ => v

/-- **Feder's theorem (bosonic, statement).**  If the single-particle host `G`
has PST from `u` to `v` at time `τ`, then the bosonic `k`-particle Feder walk
`G^{⊙k}` has PST from the all-`u` configuration to the all-`v` configuration at
the **same** time `τ`.  Concretely, `‖(bosonicWalk G k).evolve τ (diagConfig k u)
(diagConfig k v)‖ = 1`.

This is the original Feder PRL 97 180502 result: single-particle PST lifts to
`k`-boson PST on the symmetric-power host.  (Deep: the `k`-particle propagator
restricted to the symmetric subspace is the `k`-fold symmetric power of the
single-particle propagator, whose `(u…u, v…v)` element is the `k`-th power of
the single-particle PST amplitude, still of modulus one.) -/
theorem feder_bosonic_pst_lift (G : WeightedGraph V) (k : ℕ) (u v : V) (τ : ℝ)
    (_hPST : IsPST G u v τ) :
    IsPST (bosonicWalk G k) (diagConfig k u) (diagConfig k v) τ := by
  sorry

/-! ## 5.  Pair / plus-state PST

PST of the *symmetric* single-particle "plus" state `(|u⟩ + |v⟩)/√2`.  This is
the two-mode symmetric superposition whose perfect transfer is the standard
"PST of a `+`-state" notion (cf. fractional revival / plus-state transfer in the
Feder–Godsil–Tamon circle). -/

/-- The (un-normalised) **plus state** `|u⟩ + |v⟩` on the single-particle space
`V → ℂ`, as a column vector. -/
def plusState (u v : V) : V → ℂ :=
  fun w => (if w = u then 1 else 0) + (if w = v then 1 else 0)

/-- **Plus-state PST predicate.**  The normalised plus state `(|u⟩+|v⟩)/√2` is
perfectly transferred to `(|p⟩+|q⟩)/√2` at time `τ` when the single-particle
propagator `U(τ)` maps the first to a unit-modulus phase times the second:
`‖⟨(|p⟩+|q⟩)/√2| U(τ) |(|u⟩+|v⟩)/√2⟩‖ = 1`, i.e. the inner product of the
evolved (normalised) plus state with the target (normalised) plus state has
modulus one.  Concretely, with `U = G.evolve τ`,

  `‖(∑_w (plusState p q w)ᶜ · (U *ᵥ plusState u v) w) / 2‖ = 1`

(the `/2` is the product of the two `1/√2` normalisations). -/
noncomputable def IsPlusStatePST (G : WeightedGraph V) (u v p q : V) (τ : ℝ) : Prop :=
  ‖(∑ w, star (plusState p q w) * ((G.evolve τ).mulVec (plusState u v) w)) / 2‖ = 1

/-- **Plus-state PST from a swap symmetry (statement).**  If the continuous-time
walk swaps the pair `{u, v}` with the pair `{p, q}` up to a global phase — i.e.
`U(τ)` maps `|u⟩ ↦ φ|p⟩`, `|v⟩ ↦ φ|q⟩` for a unit-modulus phase `φ` — then the
plus state `(|u⟩+|v⟩)/√2` is perfectly transferred to `(|p⟩+|q⟩)/√2`.  This is
the symmetric-state PST that accompanies pairwise PST on a graph with the
relevant exchange symmetry. -/
theorem plusState_pst_of_pair_transfer (G : WeightedGraph V) (u v p q : V) (τ : ℝ)
    (φ : ℂ) (hφ : ‖φ‖ = 1) (hpq : p ≠ q)
    (hu : ∀ w, (G.evolve τ).mulVec (plusState u v) w
            = φ * plusState p q w) :
    IsPlusStatePST G u v p q τ := by
  -- Substitute the hypothesis: the inner sum becomes `φ · ∑_w |plusState p q w|²`,
  -- and on the two-element support `{p, q}` (using `p ≠ q`) that sum is `2`.
  unfold IsPlusStatePST
  have hsum : (∑ w, star (plusState p q w) * ((G.evolve τ).mulVec (plusState u v) w))
      = φ * 2 := by
    rw [Finset.sum_congr rfl (fun w _ => by rw [hu w])]
    have hfac : ∀ w, star (plusState p q w) * (φ * plusState p q w)
        = φ * (star (plusState p q w) * plusState p q w) := fun w => by ring
    rw [Finset.sum_congr rfl (fun w _ => hfac w), ← Finset.mul_sum]
    -- `∑_w star (plusState p q w) * plusState p q w = 2`.
    have hval : ∀ w, star (plusState p q w) * plusState p q w
        = (if w = p then (1 : ℂ) else 0) + (if w = q then (1 : ℂ) else 0) := by
      intro w
      unfold plusState
      by_cases hwp : w = p <;> by_cases hwq : w = q
      · exact absurd (hwp.symm.trans hwq) hpq
      · simp only [if_pos hwp, if_neg hwq, add_zero, mul_one, star_one]
      · simp only [if_neg hwp, if_pos hwq, zero_add, one_mul, star_one]
      · simp only [if_neg hwp, if_neg hwq, add_zero, mul_zero, star_zero, zero_mul]
    have hinner : (∑ w, star (plusState p q w) * plusState p q w) = 2 := by
      rw [Finset.sum_congr rfl (fun w _ => hval w), Finset.sum_add_distrib]
      rw [Finset.sum_ite_eq' Finset.univ p (fun _ => (1 : ℂ)),
          Finset.sum_ite_eq' Finset.univ q (fun _ => (1 : ℂ))]
      simp only [Finset.mem_univ, if_true]; norm_num
    rw [hinner]
  rw [hsum]
  rw [show φ * 2 / 2 = φ by ring, hφ]

end Feder

end Graphplay
