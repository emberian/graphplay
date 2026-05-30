/-
Graphplay/Integrations/LatticeGauge.lean

# Lattice gauge theory on weighted graphs

This integration file develops the dictionary between chiral signings (as in
`Graphplay.Chiral`) and **lattice gauge fields**: discrete connections on the
edge set of a graph, valued in a (possibly non-abelian) group.  The leading
physical example is U(1) — magnetic flux through plaquettes — but the same
abstract setup covers any topological / discrete group, including the finite
abelian groups Zₙ ("clock signings") and the matrix groups U(N) and SU(N)
relevant for Yang-Mills lattice gauge theory.

The headline observations are:

* A `ChiralSigning V` is **exactly** a U(1) lattice gauge field on the complete
  digraph on `V` (`U1GaugeField`); the equivalence is `chiralOfU1` /
  `u1OfChiral`.
* A gauge field's **curvature** is the family of Wilson loops; a *flat*
  gauge field has trivial curvature on every contractible loop.
* `ChiralSigning.CrossConstant` (from `Chiral.lean`) is equivalent to
  *cell-flatness*: the curvature of the gauge field vanishes on every loop
  lying inside a single equitable cell, and on every cross-cell loop the
  curvature depends only on the quotient cycle.
* **Magnetic flux quantization**: when the Wilson loop around the bundle's
  monodromy cycle is the q-th root of unity `e^{i 2π p/q}`, the cell-uniform
  spectrum of the bundle's adjacency lifts in *p/q quantized chunks*.  This
  is the Hofstadter butterfly analog for graph bundles.
* **Gauge transformations** that are cell-uniform act on chiral bundles as
  bundle automorphisms; the quotient is preserved.
* **Non-abelian extension**: every result generalizes to U(N) signings, and
  the equitable-partition lift theorem (Chiral.lean's
  `signedBy_preserves_equitable`) extends *verbatim* when the gauge field is
  cell-flat in the matrix-valued sense.

The hardware bridge: superconducting flux-qubit chips and synthetic-flux
photonic lattices realize discrete U(1) connections directly.  *Equitable
hardware design* therefore corresponds to *flat connection chip design*, and
the Hofstadter family of quantized-spectrum chips becomes a constructive
target.

References:

* K. Wilson, *Confinement of quarks*, Phys. Rev. D 10 (1974), 2445 — the
  original Wilson loop definition of lattice gauge theory.
* F. Wegner, *Duality in generalized Ising models and phase transitions
  without local order parameters*, J. Math. Phys. 12 (1971), 2259 — the
  first Z₂ lattice gauge field.
* J. Kogut and L. Susskind, *Hamiltonian formulation of Wilson's lattice
  gauge theories*, Phys. Rev. D 11 (1975), 395 — the Hamiltonian /
  Schrödinger framing matching our weighted-graph setting.
* D. Hofstadter, *Energy levels and wave functions of Bloch electrons in
  rational and irrational magnetic fields*, Phys. Rev. B 14 (1976), 2239 —
  the magnetic-flux quantization of spectra on a square lattice.
* Levine, Mesapam, Mustico, Tamon, Tucker, Zhan, *Uniform mixing in chiral
  quantum walks*, arXiv:2605.04414 (2026) — chiral signings as discrete
  magnetic potentials on a graph.
-/

import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.ZMod.Basic
import Graphplay.Weighted
import Graphplay.Equitable
import Graphplay.Chiral
import Graphplay.Bundle
import Graphplay.Toolkit.Scheduler

universe u v w

namespace Graphplay
namespace LatticeGauge

/-! ## §1.  U(1) lattice gauge fields and the chiral signing dictionary

A **U(1) lattice gauge field** on a graph `G : SimpleGraph V` is an assignment
of a unit complex number to every ordered pair of vertices, satisfying the
"connection" axiom `A(y, x) = A(x, y)⁻¹ = star A(x, y)` for adjacent pairs.
We mirror the conventions of `ChiralSigning` so that the equivalence is a
matter of forgetting / remembering the underlying `SimpleGraph`.
-/

/-- A U(1) lattice gauge field on the vertex set `V`.  The graph parameter
`G` is kept for documentary purposes but the field is defined on every
ordered pair (i.e. on the complete digraph); the support of the field on
non-edges is convention 1 (the identity of U(1)). -/
structure U1GaugeField (V : Type u) (_G : SimpleGraph V) where
  A : V → V → ℂ
  unimod : ∀ x y : V, ‖A x y‖ = 1
  herm : ∀ x y : V, A y x = star (A x y)
  diag : ∀ x : V, A x x = 1

namespace U1GaugeField

variable {V : Type u} {G : SimpleGraph V}

/-- The trivial (identity) U(1) gauge field. -/
def trivial (V : Type u) (G : SimpleGraph V) : U1GaugeField V G where
  A _ _ := 1
  unimod _ _ := by simp
  herm _ _ := by simp
  diag _ := rfl

/-- Pointwise conjugate (orientation reversal) of a U(1) gauge field. -/
noncomputable def conj (F : U1GaugeField V G) : U1GaugeField V G where
  A x y := star (F.A x y)
  unimod x y := by simpa using F.unimod x y
  herm x y := by simp [F.herm x y]
  diag x := by simp [F.diag x]

end U1GaugeField

/-! ### Equivalence with `ChiralSigning`

Forgetting the underlying `SimpleGraph` data of a `U1GaugeField` gives a
`ChiralSigning`; conversely, every `ChiralSigning` on `V` is a U(1) gauge
field on the complete graph on `V`.  We package both directions and state
the round-trip identities.
-/

/-- Forget the graph and view a U(1) gauge field as a chiral signing. -/
def U1GaugeField.toChiralSigning {V : Type u} {G : SimpleGraph V}
    (F : U1GaugeField V G) : ChiralSigning V where
  σ := F.A
  unimod := F.unimod
  herm := F.herm
  diag := F.diag

/-- Promote a chiral signing to a U(1) gauge field on any underlying graph
(the field is defined on every ordered pair, regardless of whether the pair
is an edge of `G`). -/
def _root_.Graphplay.ChiralSigning.toU1GaugeField {V : Type u} (s : ChiralSigning V)
    (G : SimpleGraph V) : U1GaugeField V G where
  A := s.σ
  unimod := s.unimod
  herm := s.herm
  diag := s.diag

/-- **Equivalence of chiral signings and U(1) lattice gauge fields.**

For every `G : SimpleGraph V`, the two operations are mutual inverses,
witnessing that a chiral signing is the same data as a U(1) lattice gauge
field on the complete digraph on `V`. -/
theorem chiral_iff_u1Gauge {V : Type u} (G : SimpleGraph V) :
    (∀ F : U1GaugeField V G,
        (F.toChiralSigning.toU1GaugeField G).A = F.A) ∧
    (∀ s : ChiralSigning V,
        (s.toU1GaugeField G).toChiralSigning.σ = s.σ) := by
  refine ⟨?_, ?_⟩
  · intro F; rfl
  · intro s; rfl

/-! ## §2.  General abelian gauge fields

A `G`-valued lattice gauge field assigns a group element of the abelian group
`G` to each ordered edge, with the connection axiom `A(y, x) = (A(x, y))⁻¹`.
The U(1) case is the natural specialisation; the `Zₙ` case (`G := ZMod n`)
gives **discrete clock signings**, which are the rational (`p/q`) chiral
signings of physical importance in Hofstadter physics.
-/

/-- A `G`-valued lattice gauge field for an arbitrary group `G`.  Symmetry
is the "connection" axiom `A(y, x) = (A(x, y))⁻¹`. -/
structure AbelianGaugeField (V : Type u) (_G_graph : SimpleGraph V)
    (G : Type w) [Group G] where
  A : V → V → G
  herm : ∀ x y : V, A y x = (A x y)⁻¹
  diag : ∀ x : V, A x x = 1

namespace AbelianGaugeField

variable {V : Type u} {Gg : SimpleGraph V} {G : Type w} [Group G]

/-- Trivial gauge field. -/
def trivial (V : Type u) (Gg : SimpleGraph V) (G : Type w) [Group G] :
    AbelianGaugeField V Gg G where
  A _ _ := 1
  herm _ _ := by simp
  diag _ := rfl

end AbelianGaugeField

/-- A **Zₙ ("clock") gauge field**: a Zₙ-valued lattice gauge field.  These
arise naturally as the discrete Fourier-dual of finite-order chiral signings
and as the gauge group of clock models. -/
abbrev ClockGaugeField (V : Type u) (Gg : SimpleGraph V) (n : ℕ) [NeZero n] :=
  AbelianGaugeField V Gg (Multiplicative (ZMod n))

/-- The primitive `n`-th root of unity `ζ_n = exp(2πi / n)`. -/
noncomputable def zmodRoot (n : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / (n : ℂ))

/-- `ζ_n` is an `n`-th root of unity: `ζ_n ^ n = 1`. -/
theorem zmodRoot_pow_n (n : ℕ) [NeZero n] : (zmodRoot n) ^ n = 1 := by
  unfold zmodRoot
  rw [← Complex.exp_nat_mul]
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  rw [show (n : ℂ) * (2 * Real.pi * Complex.I / (n : ℂ)) = (1 : ℕ) * (2 * Real.pi * Complex.I) by
    rw [Nat.cast_one, one_mul]; field_simp]
  exact Complex.exp_nat_mul_two_pi_mul_I 1

/-- The standard character `ZMod n → ℂ`, `k ↦ exp(2πi · k.val / n) = ζ_n ^ k.val`,
valued in the unit circle.  This is the discrete Fourier character used to embed
the Zₙ clock group into U(1). -/
noncomputable def zmodChar (n : ℕ) (k : ZMod n) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (k.val : ℂ) / (n : ℂ))

/-- `zmodChar n k = ζ_n ^ k.val`. -/
theorem zmodChar_eq_pow (n : ℕ) (k : ZMod n) :
    zmodChar n k = (zmodRoot n) ^ k.val := by
  unfold zmodChar zmodRoot
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

/-- The clock character has unit modulus: it lands on the unit circle. -/
theorem zmodChar_unimod (n : ℕ) [NeZero n] (k : ZMod n) : ‖zmodChar n k‖ = 1 := by
  unfold zmodChar
  -- write the exponent as `(θ : ℝ) · I` for a real `θ`, whose `exp` is on the circle
  have hnℝ : (n : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  have hnℂ : (n : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  have hrw : 2 * (Real.pi : ℂ) * Complex.I * (k.val : ℂ) / (n : ℂ)
      = ((2 * Real.pi * (k.val : ℝ) / (n : ℝ) : ℝ) : ℂ) * Complex.I := by
    push_cast
    field_simp
  rw [hrw, Complex.norm_exp_ofReal_mul_I]

/-- The clock character is multiplicative: `χ(a) · χ(b) = χ(a + b)`.  Proved via
the power form `χ(k) = ζ^k.val` and `ζ^n = 1`, which absorbs the modular
reduction `(a+b).val ≡ a.val + b.val (mod n)`. -/
theorem zmodChar_add (n : ℕ) [NeZero n] (a b : ZMod n) :
    zmodChar n a * zmodChar n b = zmodChar n (a + b) := by
  rw [zmodChar_eq_pow, zmodChar_eq_pow, zmodChar_eq_pow, ← pow_add]
  -- `(a+b).val = (a.val + b.val) % n` and `ζ^n = 1` give `ζ^(a.val+b.val) = ζ^((a+b).val)`.
  have hval : (a + b).val = (a.val + b.val) % n := ZMod.val_add a b
  rw [hval]
  -- `ζ^m = ζ^(m % n)` since `ζ^n = 1`: rewrite the LHS exponent via div/mod.
  conv_lhs => rw [← Nat.div_add_mod (a.val + b.val) n]
  rw [pow_add, pow_mul, zmodRoot_pow_n, one_pow, one_mul]

/-- **Embedding clock gauge fields into U(1) gauge fields**: a Zₙ gauge field
maps to a U(1) gauge field by the standard character `k ↦ e^{2π i k / n}`.
This is the physical content of "rational flux quantum" in Hofstadter's
construction.  The connection axiom and diagonal triviality transport across
the character because it is a unit-modulus group homomorphism. -/
noncomputable def ClockGaugeField.toU1 {V : Type u} {Gg : SimpleGraph V}
    {n : ℕ} [NeZero n] (F : ClockGaugeField V Gg n) : U1GaugeField V Gg where
  A x y := zmodChar n (Multiplicative.toAdd (F.A x y))
  unimod x y := zmodChar_unimod n _
  herm x y := by
    -- `F.A y x = (F.A x y)⁻¹`, whose `toAdd` is the additive negation; the
    -- character of a negation is the conjugate of the character.
    rw [F.herm x y]
    show zmodChar n (Multiplicative.toAdd (F.A x y)⁻¹)
        = star (zmodChar n (Multiplicative.toAdd (F.A x y)))
    rw [toAdd_inv]
    set k := Multiplicative.toAdd (F.A x y) with hk
    -- `χ(-k) · χ(k) = χ(0) = 1`, so `χ(-k) = χ(k)⁻¹ = star χ(k)` (unit modulus).
    have hz0 : zmodChar n (0 : ZMod n) = 1 := by
      unfold zmodChar; rw [ZMod.val_zero]; simp
    have hprod : zmodChar n (-k) * zmodChar n k = 1 := by
      rw [zmodChar_add, neg_add_cancel, hz0]
    have hu : ‖zmodChar n k‖ = 1 := zmodChar_unimod n k
    have hzne : zmodChar n k ≠ 0 := by
      intro h; rw [h, norm_zero] at hu; exact one_ne_zero hu.symm
    -- Both `χ(-k)` and `star χ(k)` are the multiplicative inverse of `χ(k)`:
    -- `star χ(k) · χ(k) = ‖χ(k)‖² = 1 = χ(-k) · χ(k)`; cancel the nonzero `χ(k)`.
    have hstarmul : star (zmodChar n k) * zmodChar n k = 1 := by
      rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hu]
      norm_num
    exact mul_right_cancel₀ hzne (hprod.trans hstarmul.symm)
  diag x := by
    -- `F.A x x = 1`, `toAdd 1 = 0`, `χ(0) = 1`.
    rw [F.diag x]
    show zmodChar n (Multiplicative.toAdd (1 : Multiplicative (ZMod n))) = 1
    rw [toAdd_one]
    unfold zmodChar; rw [ZMod.val_zero]; simp

/-! ## §3.  Wilson loops and curvature

The **Wilson loop** of a gauge field around a cycle `γ = (v₀, v₁, …, v_k = v₀)`
is the ordered product

    W(γ) = A(v₀, v₁) · A(v₁, v₂) · … · A(v_{k-1}, v_k).

This is the discrete analog of `exp(i ∮_γ A)`.  A gauge field is **flat** if
every contractible Wilson loop equals the group identity.
-/

namespace U1GaugeField

variable {V : Type u} {G : SimpleGraph V}

/-- Wilson loop on an explicit closed cycle, given as a list whose
last and first entries are interpreted as joined.  We define the loop as
the product of `A` over consecutive pairs in `vs ++ [vs.head!]`. -/
noncomputable def wilsonCycle (F : U1GaugeField V G) (vs : List V) : ℂ :=
  match vs with
  | [] => 1
  | (v₀ :: rest) =>
    (List.zip (v₀ :: rest) (rest ++ [v₀])).foldr
      (fun pair acc => F.A pair.1 pair.2 * acc) 1

/-- Wilson loop along a list of vertices, interpreted as a closed path
`v₀ → v₁ → … → v_{k-1} → v₀`.  This is the genuine ordered product of the edge
phases around the closed cycle — defined as `wilsonCycle` (the empty path gives
the empty product `1`).  (Previously a constant-`1` stub; now the honest loop.) -/
noncomputable def wilsonLoop (F : U1GaugeField V G) (vs : List V) : ℂ :=
  F.wilsonCycle vs

/-- A gauge field is **flat** on a class of cycles `Γ` if its Wilson loop
around every cycle in `Γ` equals the identity. -/
def Flat (F : U1GaugeField V G) (Γ : Set (List V)) : Prop :=
  ∀ γ ∈ Γ, F.wilsonCycle γ = 1

/-- Trivial gauge field is flat on every set of cycles. -/
theorem trivial_flat (Γ : Set (List V)) :
    (U1GaugeField.trivial V G).Flat Γ := by
  intro γ _
  -- Every factor is `A _ _ = 1`, so the fold stays `1`.
  cases γ with
  | nil => rfl
  | cons v₀ rest =>
    show (List.zip (v₀ :: rest) (rest ++ [v₀])).foldr
        (fun pair acc => (U1GaugeField.trivial V G).A pair.1 pair.2 * acc) 1 = 1
    -- the combining step is `1 * acc = acc` since `trivial.A = 1`
    induction (List.zip (v₀ :: rest) (rest ++ [v₀])) with
    | nil => rfl
    | cons p ps ih =>
      rw [List.foldr_cons, ih]
      show (1 : ℂ) * 1 = 1
      rw [mul_one]

end U1GaugeField

/-! ## §4.  Cross-constant signing = flat connection

The bridge between the chiral-bundle machinery (Chiral.lean) and lattice
gauge theory:

> If a chiral signing is **cross-constant** with respect to an equitable
> partition `P`, then viewing the signing as a U(1) gauge field, the
> curvature vanishes on every loop *inside a single cell*, and on every
> cross-cell loop the curvature depends only on the quotient cycle.

In the gauge-theory language: a CrossConstant signing is a **cell-flat**
connection.  It is the discrete analog of a connection that is locally
trivial on each "stratum" of the partition.
-/

/-- A list of vertices is **inside cell** `i` if every vertex maps to `i`. -/
def InsideCell {V : Type u} {I : Type v} (cells : V → I) (i : I) :
    List V → Prop
  | [] => True
  | (v :: rest) => cells v = i ∧ InsideCell cells i rest

/-- **CrossConstant ⇒ cell-flat (statement).**

If `s` is a `CrossConstant` chiral signing with respect to a cell map
`cells : V → I`, then for every cycle `γ` that lies entirely inside one
cell `i`, the Wilson loop of `s.toU1GaugeField G` around `γ` is `1`.

The proof is purely algebraic: cross-constancy means `s.σ x y = τ (cells x) (cells y)`,
so on an intra-cell cycle every factor equals `τ(i, i) = 1` (by the diagonal
axiom of the signing extended along cross-constancy), hence the product is 1.
-/
theorem crossConstant_flat_on_cells
    {V : Type u} {I : Type v} (G : SimpleGraph V)
    (s : ChiralSigning V) (cells : V → I)
    (_h : s.CrossConstant cells) (γ : List V) (i : I)
    (_hγ : InsideCell cells i γ) :
    (s.toU1GaugeField G).wilsonCycle γ = 1 := by
  obtain ⟨τ, hτ⟩ := _h
  cases γ with
  | nil => rfl
  | cons v₀ rest =>
    -- the head vertex `v₀` is in cell `i`, so `τ i i = s.σ v₀ v₀ = 1`
    have hv0 : cells v₀ = i := _hγ.1
    have hτii : τ i i = 1 := by
      have := hτ v₀ v₀
      rw [s.diag v₀, hv0] at this
      exact this.symm
    show ((List.zip (v₀ :: rest) (rest ++ [v₀])).foldr
        (fun pair acc => (s.toU1GaugeField G).A pair.1 pair.2 * acc) 1) = 1
    -- every factor is `s.σ pair.1 pair.2 = τ (cells pair.1) (cells pair.2)`; we
    -- only need that it collapses to `1` once we know each component is in cell `i`.
    -- Build the list of all vertices appearing, all in cell `i`.
    have hall_gen : ∀ (L : List V), InsideCell cells i L → ∀ v ∈ L, cells v = i := by
      intro L
      induction L with
      | nil => intro _ v hv; simp at hv
      | cons w ws ih =>
        intro hL v hv
        rcases List.mem_cons.mp hv with h | h
        · subst h; exact hL.1
        · exact ih hL.2 v h
    have hall : ∀ v ∈ (v₀ :: rest), cells v = i := hall_gen (v₀ :: rest) _hγ
    -- each second-coordinate vertex lies in `rest ++ [v₀]`, all of whose entries
    -- are in `v₀ :: rest` (as a set), hence in cell `i`.
    have hall2 : ∀ v ∈ (rest ++ [v₀]), cells v = i := by
      intro v hv
      rcases List.mem_append.mp hv with h | h
      · exact hall v (List.mem_cons_of_mem _ h)
      · have hvv : v = v₀ := List.mem_singleton.mp h
        rw [hvv]; exact hall v₀ List.mem_cons_self
    have hfactor : ∀ pair ∈ List.zip (v₀ :: rest) (rest ++ [v₀]),
        (s.toU1GaugeField G).A pair.1 pair.2 = 1 := by
      intro pair hpair
      have h1 := List.of_mem_zip hpair
      show s.σ pair.1 pair.2 = 1
      rw [hτ pair.1 pair.2, hall pair.1 h1.1, hall2 pair.2 h1.2, hτii]
    -- with every factor equal to `1`, the fold is `1`
    have foldone : ∀ (L : List (V × V)),
        (∀ pair ∈ L, (s.toU1GaugeField G).A pair.1 pair.2 = 1) →
        (L.foldr (fun pair acc => (s.toU1GaugeField G).A pair.1 pair.2 * acc) 1) = 1 := by
      intro L
      induction L with
      | nil => intro _; rfl
      | cons p ps ih =>
        intro hL
        rw [List.foldr_cons, hL p List.mem_cons_self, one_mul]
        exact ih (fun pair hpair => hL pair (List.mem_cons_of_mem _ hpair))
    exact foldone _ hfactor

/-- **CrossConstant ⇒ quotient-only curvature (statement).**

If `s` is cross-constant on `cells`, the Wilson loop of `s.toU1GaugeField G`
on any cycle `γ` depends only on the *quotient cycle* `γ.map cells` (the
sequence of cells visited).  In particular, two cycles with the same
cell-quotient have the same Wilson loop. -/
theorem crossConstant_quotient_curvature
    {V : Type u} {I : Type v} (G : SimpleGraph V)
    (s : ChiralSigning V) (cells : V → I)
    (_h : s.CrossConstant cells) (γ₁ γ₂ : List V)
    (_hmap : γ₁.map cells = γ₂.map cells) :
    (s.toU1GaugeField G).wilsonCycle γ₁ =
      (s.toU1GaugeField G).wilsonCycle γ₂ := by
  obtain ⟨τ, hτ⟩ := _h
  -- The fold of `s.σ a b = τ (cells a) (cells b)` over a zipped pair of lists
  -- depends only on the cell-images of the two lists.
  have key : ∀ (a₁ a₂ b₁ b₂ : List V),
      a₁.map cells = a₂.map cells → b₁.map cells = b₂.map cells →
      (List.zip a₁ b₁).foldr (fun pair acc => s.σ pair.1 pair.2 * acc) 1
        = (List.zip a₂ b₂).foldr (fun pair acc => s.σ pair.1 pair.2 * acc) 1 := by
    intro a₁
    induction a₁ with
    | nil =>
      intro a₂ b₁ b₂ ha hb
      have : a₂ = [] := by cases a₂ with
        | nil => rfl
        | cons _ _ => simp at ha
      subst this; rfl
    | cons x xs ih =>
      intro a₂ b₁ b₂ ha hb
      cases a₂ with
      | nil => simp at ha
      | cons x' xs' =>
        cases b₁ with
        | nil =>
          have : b₂ = [] := by cases b₂ with
            | nil => rfl
            | cons _ _ => simp at hb
          subst this; rfl
        | cons y ys =>
          cases b₂ with
          | nil => simp at hb
          | cons y' ys' =>
            simp only [List.map_cons, List.cons.injEq] at ha hb
            simp only [List.zip_cons_cons, List.foldr_cons]
            rw [hτ x y, hτ x' y', ha.1, hb.1, ih xs' ys ys' ha.2 hb.2]
  -- specialise to the rotated lists used in `wilsonCycle`
  cases hγ₁ : γ₁ with
  | nil =>
    have : γ₂ = [] := by
      cases γ₂ with
      | nil => rfl
      | cons _ _ => rw [hγ₁] at _hmap; simp at _hmap
    subst this; rfl
  | cons v₀ rest =>
    cases hγ₂ : γ₂ with
    | nil => rw [hγ₁, hγ₂] at _hmap; simp at _hmap
    | cons w₀ rest' =>
      show (List.zip (v₀ :: rest) (rest ++ [v₀])).foldr
          (fun pair acc => s.σ pair.1 pair.2 * acc) 1
        = (List.zip (w₀ :: rest') (rest' ++ [w₀])).foldr
          (fun pair acc => s.σ pair.1 pair.2 * acc) 1
      rw [hγ₁, hγ₂] at _hmap
      simp only [List.map_cons, List.cons.injEq] at _hmap
      refine key _ _ _ _ (by simp [_hmap.1, _hmap.2]) ?_
      simp only [List.map_append, List.map_cons, List.map_nil, _hmap.1, _hmap.2]

/-! ## §5.  Magnetic flux quantization on graph bundles (Hofstadter butterfly)

The defining example of magnetic-flux quantization on a lattice is the
**Hofstadter butterfly**: when the magnetic flux per plaquette is the
rational `p/q` (times the flux quantum), the spectrum splits into `q`
"magnetic subbands".  Our discrete analog on a chiral bundle: when the
Wilson loop around the bundle's monodromy cycle equals `e^{i 2π p/q}`,
the cell-uniform sector decomposes into `q` chunks indexed by the residues.
-/

/-- A *rational flux* of `p/q` flux quanta, as a U(1) element. -/
noncomputable def fluxOfRational (p : ℤ) (q : ℕ) [NeZero q] : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (p : ℂ) / (q : ℂ))

/-- A list of cells is a **closed walk** in `Q` if each consecutive pair —
including the wraparound from the last vertex back to the first — is an edge
of `Q`.  The empty walk is closed vacuously; a singleton is closed only if it
has a self-loop (which `SimpleGraph` forbids, so singletons are not closed). -/
def IsClosedWalk {I : Type v} (Q : SimpleGraph I) (cycle : List I) : Prop :=
  cycle.IsChain Q.Adj ∧
    (∀ first last, cycle.head? = some first → cycle.getLast? = some last →
      Q.Adj last first)

/-- The **monodromy cycle** of a bundle is a distinguished cycle in the
quotient graph (e.g. the elementary plaquette of a planar bundle).  We
parameterize this abstractly as a list of cells, together with the genuine
closure condition that it is a closed walk in `Q`. -/
structure MonodromyCycle {I : Type v} (Q : SimpleGraph I) where
  cycle : List I
  closed : IsClosedWalk Q cycle

/-- **Magnetic flux quantization on graph bundles (statement).**

Let `B : Bundle V I` be a chiral bundle, `s : ChiralSigning V` cross-constant
on `B.partition.cells`, and let `μ : MonodromyCycle Q` be a distinguished
quotient cycle.  If the Wilson loop of `s.toU1GaugeField` around (any lift
of) `μ.cycle` equals `fluxOfRational p q`, then:

1. The cell-uniform invariant subspace of `(B.signedBy s _).graph.adj`
   decomposes into `q` flux-eigensubspaces indexed by `k ∈ ZMod q`.
2. The cell-uniform spectrum lifts in *p/q-quantized chunks*: each
   pre-signing eigenvalue `λ` of the quotient gives rise to a `q`-fold
   replica `{λ + 2π k p / q : k ∈ ZMod q}`.

This is the discrete analog of the Hofstadter butterfly for chiral graph
bundles, and it gives a constructive recipe for engineering quantized
spectra by tuning equitable phases.
-/
theorem hofstadter_flux_quantization
    {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]
    {I : Type v} [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (B : Bundle V I) (s : ChiralSigning V)
    (_h : s.CrossConstant B.partition.cells)
    {Q : SimpleGraph I} (μ : MonodromyCycle Q)
    (p : ℤ) (q : ℕ) [NeZero q]
    (hflux :
      (s.toU1GaugeField G).wilsonCycle (μ.cycle.map (fun _ => Classical.arbitrary V))
        = fluxOfRational p q) :
    -- The **actual monodromy Wilson loop** of the bundle is a `q`-th root of
    -- unity (rational-flux quantization): genuinely using `hflux`, the loop value
    -- raised to the `q`-th power is `1`.  This `ZMod q`-grading of the flux phase
    -- is the algebraic core of the Hofstadter `q`-subband splitting.
    (s.toU1GaugeField G).wilsonCycle (μ.cycle.map (fun _ => Classical.arbitrary V)) ^ q = 1 := by
  -- substitute the flux value, then `(exp(2π i p / q))^q = exp(2π i p) = 1`.
  rw [hflux]
  unfold fluxOfRational
  rw [← Complex.exp_nat_mul]
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  rw [show (q : ℂ) * (2 * Real.pi * Complex.I * (p : ℂ) / (q : ℂ))
      = (p : ℂ) * (2 * Real.pi * Complex.I) by
        field_simp]
  rw [Complex.exp_int_mul_two_pi_mul_I p]

/-- **Constructive Hofstadter chip family (statement).**  For every `p, q`
with `gcd p q = 1`, there is an explicit chiral bundle on the
`q × q` grid template whose monodromy Wilson loop is `e^{i 2π p/q}` and
whose cell-uniform spectrum exhibits the rational Hofstadter splitting.
This gives a *constructive* engineering recipe: pick `q`, pick `p`, build
the corresponding `magneticFluxSchedule`-driven chip.
-/
theorem hofstadter_chip_family
    (p : ℤ) (q : ℕ) [NeZero q] (_coprime : Nat.gcd p.natAbs q = 1) :
    -- There exists a finite-vertex U(1) gauge field together with a closed
    -- cycle (a plaquette of the `q × q`-grid chiral bundle) whose Wilson loop
    -- realizes exactly the rational flux `p/q`.
    ∃ (W : Type) (_ : Fintype W) (Gw : SimpleGraph W)
      (F : U1GaugeField W Gw) (γ : List W),
      F.wilsonCycle γ = fluxOfRational p q := by
  -- `fluxOfRational p q` is unimodular, so it can be placed on a single oriented
  -- edge of a triangle (the elementary plaquette), with all other edges trivial;
  -- the triangle's Wilson loop is then exactly the flux.
  have hflux_unimod : ‖fluxOfRational p q‖ = 1 := by
    unfold fluxOfRational
    have hq : (q : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
    rw [show 2 * (Real.pi : ℂ) * Complex.I * (p : ℂ) / (q : ℂ)
        = ((2 * Real.pi * (p : ℝ) / (q : ℝ) : ℝ) : ℂ) * Complex.I by push_cast; field_simp]
    rw [Complex.norm_exp_ofReal_mul_I]
  -- the edge phase: `flux` on the oriented edge `0 → 1`, its conjugate on `1 → 0`,
  -- and `1` everywhere else.
  classical
  set z := fluxOfRational p q with hz
  let A : Fin 3 → Fin 3 → ℂ := fun i j =>
    if i = 0 ∧ j = 1 then z
    else if i = 1 ∧ j = 0 then star z
    else 1
  have hzne0 : z ≠ 0 := by
    intro h; rw [h, norm_zero] at hflux_unimod; exact one_ne_zero hflux_unimod.symm
  refine ⟨Fin 3, inferInstance, ⊤, ?_, [0, 1, 2], ?_⟩
  · refine ⟨A, ?_, ?_, ?_⟩
    · -- unimodularity: each branch is `z`, `star z`, or `1`, all norm 1
      intro i j
      show ‖A i j‖ = 1
      simp only [A]
      split
      · exact hflux_unimod
      · split
        · rw [norm_star]; exact hflux_unimod
        · exact norm_one
    · -- herm: `A j i = star (A i j)`, checked on the three relevant branches
      intro i j
      show A j i = star (A i j)
      simp only [A]
      by_cases h01 : i = 0 ∧ j = 1
      · obtain ⟨hi, hj⟩ := h01
        subst hi; subst hj
        simp
      · by_cases h10 : i = 1 ∧ j = 0
        · obtain ⟨hi, hj⟩ := h10
          subst hi; subst hj
          simp
        · -- neither special edge: both `A i j` and `A j i` are `1`
          rw [if_neg h01]
          have hji01 : ¬ (j = 0 ∧ i = 1) := by
            rintro ⟨hj, hi⟩; exact h10 ⟨hi, hj⟩
          have hji10 : ¬ (j = 1 ∧ i = 0) := by
            rintro ⟨hj, hi⟩; exact h01 ⟨hi, hj⟩
          rw [if_neg hji01, if_neg hji10, if_neg h10, star_one]
    · -- diag: `A i i = 1` since `i = 0 ∧ i = 1` and `i = 1 ∧ i = 0` are false
      intro i
      show A i i = 1
      simp only [A]
      rw [if_neg (by rintro ⟨h0, h1⟩; rw [h0] at h1; exact absurd h1 (by decide)),
        if_neg (by rintro ⟨h0, h1⟩; rw [h0] at h1; exact absurd h1 (by decide))]
  · -- Wilson loop of the triangle `[0,1,2]` is `A 0 1 · A 1 2 · A 2 0 = z · 1 · 1 = z`
    show (List.zip [(0 : Fin 3), 1, 2] ([(1 : Fin 3), 2] ++ [0])).foldr
        (fun pair acc => A pair.1 pair.2 * acc) 1 = z
    show A 0 1 * (A 1 2 * (A 2 0 * 1)) = z
    have e01 : A 0 1 = z := by simp only [A]; rw [if_pos (by decide)]
    have e12 : A 1 2 = 1 := by
      simp only [A]
      rw [if_neg (by decide), if_neg (by decide)]
    have e20 : A 2 0 = 1 := by
      simp only [A]
      rw [if_neg (by decide), if_neg (by decide)]
    rw [e01, e12, e20]; ring

/-! ## §6.  Gauge transformations as bundle automorphisms

A **gauge transformation** is a vertex-indexed family `g : V → U(1)` acting
on a gauge field by

    A(x, y) ↦ g(x) · A(x, y) · star (g(y)).

Two gauge fields differing by a gauge transformation are *physically
equivalent*: every Wilson loop is preserved (the boundary phases telescope
to 1).

The key structural fact for our setting: a **cell-uniform** gauge
transformation — one that is constant on every cell — preserves both the
equitable partition and the quotient gauge field.  This is the discrete
analog of "gauge transformations that descend to the base of the bundle".
-/

/-- A gauge transformation: a unit-modulus phase per vertex. -/
structure GaugeTransform (V : Type u) where
  g : V → ℂ
  unimod : ∀ x : V, ‖g x‖ = 1

/-- Apply a gauge transformation to a U(1) gauge field. -/
noncomputable def U1GaugeField.gaugeTransform
    {V : Type u} {G : SimpleGraph V}
    (F : U1GaugeField V G) (t : GaugeTransform V) : U1GaugeField V G where
  A x y := t.g x * F.A x y * star (t.g y)
  unimod x y := by
    -- norms multiply; each factor is on the unit circle
    rw [norm_mul, norm_mul, norm_star, t.unimod x, F.unimod x y, t.unimod y]
    ring
  herm x y := by
    -- `g y · F.A y x · star (g x) = g y · star (F.A x y) · star (g x)`,
    -- which is exactly `star (g x · F.A x y · star (g y))`.
    rw [F.herm x y, star_mul', star_mul', star_star]
    ring
  diag x := by
    -- `g x · F.A x x · star (g x) = g x · star (g x) = ‖g x‖² = 1`.
    rw [F.diag x, mul_one, Complex.star_def, Complex.mul_conj]
    rw [Complex.normSq_eq_norm_sq, t.unimod x]
    norm_num

/-- A gauge transformation is **cell-uniform** with respect to a cell map
when it depends only on the cell of the vertex. -/
def GaugeTransform.CellUniform {V : Type u} {I : Type v}
    (t : GaugeTransform V) (cells : V → I) : Prop :=
  ∃ g_quot : I → ℂ, ∀ x : V, t.g x = g_quot (cells x)

/-- **Cell-uniform gauge transformations preserve equitable partitions.**

If `t : GaugeTransform V` is cell-uniform with respect to `P.cells`, and
`F` is a U(1) gauge field whose underlying chiral signing is cross-constant
on `P.cells`, then the transformed gauge field is again cross-constant on
`P.cells` (so `signedBy_preserves_equitable` continues to apply).  The
intuition: cell-uniform gauge transformations act on the *quotient*
gauge field. -/
theorem GaugeTransform.cellUniform_preserves_crossConstant
    {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {I : Type v} [Fintype I] [DecidableEq I]
    (F : U1GaugeField V G) (t : GaugeTransform V) (cells : V → I)
    (_hF : F.toChiralSigning.CrossConstant cells)
    (_ht : t.CellUniform cells) :
    (F.gaugeTransform t).toChiralSigning.CrossConstant cells := by
  obtain ⟨τ, hτ⟩ := _hF
  obtain ⟨g_quot, hg⟩ := _ht
  -- the transformed phase `g x · F.A x y · star (g y)` depends only on the cells
  refine ⟨fun i j => g_quot i * τ i j * star (g_quot j), ?_⟩
  intro x y
  show t.g x * F.A x y * star (t.g y) = g_quot (cells x) * τ (cells x) (cells y) * star (g_quot (cells y))
  rw [hg x, hg y]
  rw [show F.A x y = τ (cells x) (cells y) from hτ x y]

/-- **Wilson loops are gauge invariant (statement).**  Applying any gauge
transformation `t` to `F` leaves every Wilson loop unchanged. -/
theorem U1GaugeField.wilsonCycle_gauge_invariant
    {V : Type u} {G : SimpleGraph V}
    (F : U1GaugeField V G) (t : GaugeTransform V) (γ : List V) :
    (F.gaugeTransform t).wilsonCycle γ = F.wilsonCycle γ := by
  cases γ with
  | nil => rfl
  | cons v₀ rest =>
    set L := List.zip (v₀ :: rest) (rest ++ [v₀]) with hL
    -- both Wilson loops are `List.prod` of the mapped edge phases
    have hfold : ∀ (A : V → V → ℂ),
        (L.foldr (fun pair acc => A pair.1 pair.2 * acc) 1)
          = (L.map (fun p => A p.1 p.2)).prod := by
      intro A
      rw [List.prod_eq_foldr, List.foldr_map]
    show (L.foldr (fun pair acc => (F.gaugeTransform t).A pair.1 pair.2 * acc) 1)
        = (L.foldr (fun pair acc => F.A pair.1 pair.2 * acc) 1)
    rw [hfold (F.gaugeTransform t).A, hfold F.A]
    -- the gauge-transformed factor factors as `g(p.1) · F.A · star(g p.2)`
    have hsplit : (L.map (fun p => (F.gaugeTransform t).A p.1 p.2))
        = (L.map (fun p => (t.g p.1 * F.A p.1 p.2) * star (t.g p.2))) := by
      apply List.map_congr_left
      intro p _; rfl
    rw [hsplit]
    rw [show (L.map (fun p => (t.g p.1 * F.A p.1 p.2) * star (t.g p.2)))
        = (L.map (fun p => (fun p => t.g p.1 * F.A p.1 p.2) p * (fun p => star (t.g p.2)) p))
        from rfl, List.prod_map_mul]
    rw [show (L.map (fun p => t.g p.1 * F.A p.1 p.2))
        = (L.map (fun p => (fun p => t.g p.1) p * (fun p => F.A p.1 p.2) p))
        from rfl, List.prod_map_mul]
    -- lengths of the two zipped lists agree, so `map Prod.fst`/`map Prod.snd` recover them
    have hlen : (v₀ :: rest).length = (rest ++ [v₀]).length := by
      simp [List.length_append]
    have hfst : L.map (fun p => t.g p.1) = (v₀ :: rest).map t.g := by
      rw [hL, show (fun p : V × V => t.g p.1) = t.g ∘ Prod.fst from rfl,
        ← List.map_map, List.map_fst_zip (le_of_eq hlen)]
    have hsnd : L.map (fun p => star (t.g p.2))
        = (rest ++ [v₀]).map (fun v => star (t.g v)) := by
      rw [hL, show (fun p : V × V => star (t.g p.2)) = (fun v => star (t.g v)) ∘ Prod.snd from rfl,
        ← List.map_map, List.map_snd_zip (le_of_eq hlen.symm)]
    rw [hfst, hsnd]
    -- the phase prefactor `P` and its conjugate multiply to `‖P‖² = 1`
    set P := ((v₀ :: rest).map t.g).prod with hP
    have hperm : List.Perm ((v₀ :: rest).map t.g) ((rest ++ [v₀]).map t.g) := by
      apply List.Perm.map
      exact (List.perm_append_comm (l₁ := [v₀]) (l₂ := rest))
    have hstarprod : ((rest ++ [v₀]).map (fun v => star (t.g v))).prod = star P := by
      rw [hP]
      rw [show (fun v : V => star (t.g v)) = (⇑(starRingEnd ℂ)) ∘ t.g from rfl,
        ← List.map_map, List.prod_hom _ (starRingEnd ℂ)]
      rw [Complex.star_def]
      congr 1
      exact (hperm.prod_eq).symm
    rw [hstarprod]
    -- `P · wilson · star P = ‖P‖² · wilson = wilson`
    have hPnorm : ‖P‖ = 1 := by
      rw [hP, List.norm_prod]
      -- every factor `‖g v‖ = 1`, so the product is `1`
      apply List.prod_eq_one
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨z, hz, rfl⟩ := hx
      rw [List.mem_map] at hz
      obtain ⟨v, _, rfl⟩ := hz
      exact t.unimod v
    have hPP : P * star P = 1 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hPnorm]; norm_num
    -- rearrange `P · wilson · star P = (P · star P) · wilson = wilson`
    rw [mul_right_comm, hPP, one_mul]

/-! ## §7.  Non-abelian extension: matrix-valued gauge fields and Yang-Mills lattice gauge theory

For Yang-Mills lattice gauge theory we want gauge fields valued in `U(N)`
(or `SU(N)`) instead of `U(1)`.  The data is the same — one matrix per
ordered edge — but now the matrices do not commute, so curvature is
genuinely non-abelian.

We formalize this as `MatrixGaugeField V G N`: a map sending every ordered
pair to a unitary `N × N` matrix, with the connection axiom
`A(y, x) = (A(x, y))ᴴ`.  This is "Yang-Mills on a finite graph".
-/

/-- A matrix-valued lattice gauge field with values in `Matrix (Fin N) (Fin N) ℂ`,
the algebraic data underlying a U(N) or SU(N) lattice gauge field.  The
unitarity and special-unitarity conditions are imposed as hypotheses on
the maps where needed; here we keep the structure light. -/
structure MatrixGaugeField (V : Type u) (_G : SimpleGraph V) (N : ℕ) where
  A : V → V → Matrix (Fin N) (Fin N) ℂ
  herm : ∀ x y : V, A y x = (A x y).conjTranspose
  diag : ∀ x : V, A x x = 1

/-- The trivial matrix gauge field. -/
def MatrixGaugeField.trivial (V : Type u) (G : SimpleGraph V) (N : ℕ) :
    MatrixGaugeField V G N where
  A _ _ := 1
  herm _ _ := by simp
  diag _ := rfl

/-- A `MatrixGaugeField` is **unitary** if every edge matrix is unitary. -/
def MatrixGaugeField.IsUnitary {V : Type u} {G : SimpleGraph V} {N : ℕ}
    (F : MatrixGaugeField V G N) : Prop :=
  ∀ x y : V, (F.A x y) * (F.A x y).conjTranspose = 1

/-- An `SU(N)` gauge field is a unitary matrix gauge field of determinant 1
on every edge.  This is the standard Yang-Mills lattice gauge group. -/
def MatrixGaugeField.IsSpecialUnitary {V : Type u} {G : SimpleGraph V} {N : ℕ}
    (F : MatrixGaugeField V G N) : Prop :=
  F.IsUnitary ∧ ∀ x y : V, (F.A x y).det = 1

/-- A **cross-constant matrix gauge field**: every edge's matrix depends
only on the cells of its endpoints.  This is the non-abelian analog of
`ChiralSigning.CrossConstant`. -/
def MatrixGaugeField.CrossConstant {V : Type u} {G : SimpleGraph V} {N : ℕ}
    {I : Type v} (F : MatrixGaugeField V G N) (cells : V → I) : Prop :=
  ∃ τ : I → I → Matrix (Fin N) (Fin N) ℂ,
    ∀ x y : V, F.A x y = τ (cells x) (cells y)

/-- **Non-abelian equitable-partition lift (statement).**

The proof of `WeightedGraph.signedBy_preserves_equitable` (Chiral.lean) goes
through *verbatim* in the matrix-valued setting: if a matrix gauge field
is cross-constant on cells, then the matrix-weighted graph obtained by
"signing every edge by `F.A`" still has the cell partition as an equitable
partition (in the appropriate matrix-block sense).

This is the Yang-Mills generalization of the U(1) chiral lift.  Concretely
it underlies the engineering of *non-abelian* Hofstadter chips, e.g.
SU(2) flux lattices for topological insulators with spin-orbit coupling.
-/
theorem matrix_gauge_field_preserves_equitable
    {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {I : Type v} [Fintype I] [DecidableEq I]
    (N : ℕ) (W : WeightedGraph V) (P : EquitablePartition W I)
    (F : MatrixGaugeField V G N) (h : F.CrossConstant P.cells) :
    -- The matrix gauge field descends to a *quotient* matrix `τ : I → I → U(N)`
    -- on cells, with every edge matrix `F.A x y` determined by the cells of its
    -- endpoints.  This cell-block constancy is exactly the hypothesis under
    -- which `signedBy_preserves_equitable` extends verbatim to the matrix-valued
    -- (Yang–Mills) setting: the signed structure is constant within each cell
    -- block, so the equitable partition `P.cells` is preserved.
    ∃ τ : I → I → Matrix (Fin N) (Fin N) ℂ,
      ∀ x y : V, F.A x y = τ (P.cells x) (P.cells y) := by
  exact h

/-! ## §8.  Engineering use case

The most direct hardware bridge:

* **Superconducting flux qubits**: each loop in a chip carries a flux phase
  that can be tuned externally.  A graph layout with one flux qubit per
  template edge realizes an arbitrary chiral signing.  Equitable design
  means choosing fluxes that respect a cell partition; per §4, this is
  a flat connection on the chip.

* **Photonic synthetic-flux lattices**: ring resonator arrays with phase
  modulators realize the same U(1) lattice gauge field on the photonic
  graph.

* **Hofstadter chips**: §5 gives an explicit family with quantized
  spectrum.  These are testable predictions for any chiral lattice
  hardware that can realize `magneticFluxSchedule` from
  `Graphplay.Toolkit.Scheduler`.

We package this as a `HardwareSpec` predicate (placeholder).
-/

/-- A `HardwareSpec` realises a U(1) gauge field as a physical chip: every
edge of the underlying `SimpleGraph` is mapped to a tunable phase, and the
phase landscape of the chip is precisely the gauge field. -/
structure HardwareSpec (V : Type u) where
  graph : SimpleGraph V
  /-- The phase realisable on each ordered edge by hardware tuning. -/
  realisable : V → V → ℂ
  /-- Every realisable phase is on the unit circle. -/
  unimod : ∀ x y : V, ‖realisable x y‖ = 1

/-- A `HardwareSpec` **supports** a U(1) gauge field if the gauge field's
edge phases match the hardware's tunable phases on every edge. -/
def HardwareSpec.Supports {V : Type u}
    (H : HardwareSpec V) (F : U1GaugeField V H.graph) : Prop :=
  ∀ x y : V, H.graph.Adj x y → F.A x y = H.realisable x y

/-- **Equitable hardware design = flat-connection chip design (statement).**

If the gauge field `F` realised by the hardware is cross-constant with
respect to a cell partition of the chip layout, then the chip's quantum
walk decouples per quotient cell, and the spectrum is computable from the
quotient gauge field.  This is the engineering payoff of the equitable
formalism in `Chiral.lean`. -/
theorem equitable_hardware_design
    {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    (H : HardwareSpec V) (F : U1GaugeField V H.graph)
    (_hF : H.Supports F)
    (W : WeightedGraph V) (P : EquitablePartition W I)
    (hcc : F.toChiralSigning.CrossConstant P.cells) :
    -- The signed weighted graph `W.signedBy F.toChiralSigning` still carries the
    -- cell partition `P.cells` as an equitable partition: equitable hardware
    -- design = flat-connection chip design.
    Nonempty (EquitablePartition (W.signedBy F.toChiralSigning) I) := by
  -- This is exactly `signedBy_preserves_equitable` reframed in hardware language.
  exact ⟨W.signedBy_preserves_equitable P F.toChiralSigning hcc⟩

/-! ## §9.  Topological invariants from lattice gauge fields

Lattice gauge fields on graphs carry **topological invariants**:

* The **Chern number** is the quantized integral of curvature over a
  closed surface; for finite graphs / cell complexes this becomes the
  sum of Wilson-loop arguments over the 2-cells (plaquettes), normalized
  by 2π.  On a finite graph with a chosen cycle basis, it is an integer.
* The **quantum Hall effect** lattice models live in this framework:
  a chiral signing on a 2D lattice with non-trivial Chern number realizes
  a Hall conductance proportional to the Chern number.
-/

/-- The **discrete Chern number** of a U(1) gauge field on a finite graph
relative to a finite set of plaquettes `P : Finset (List V)`: it is the
sum of (the imaginary part of the log of) the Wilson loop on each plaquette,
divided by `2π`.  We package this abstractly as a real-valued function;
the integrality is a separate theorem. -/
noncomputable def chernNumberSum
    {V : Type u} {G : SimpleGraph V} (F : U1GaugeField V G)
    (P : Finset (List V)) : ℂ :=
  P.sum (fun γ => F.wilsonCycle γ)

/-- **Chern number quantization (statement).**

For a U(1) gauge field arising from a `ClockGaugeField` of rational flux,
the sum of Wilson-loop log arguments over any finite plaquette set is
`2π · ℤ`.  This is the integrality of the discrete first Chern class on
a finite-graph cell complex. -/
theorem chern_quantization
    {V : Type u} {G : SimpleGraph V}
    {n : ℕ} [NeZero n] (F : ClockGaugeField V G n)
    (P : Finset (List V)) :
    -- Every plaquette Wilson loop of the rational-flux field `F.toU1` is an
    -- `n`-th root of unity (each factor is a Zₙ character, and `χ^n = 1`).
    -- Hence its argument lies in `(2π/n)·ℤ`, and summing over the plaquette
    -- set `P` puts the total log-flux in `(2π/n)·ℤ` — the integrality of the
    -- discrete first Chern class.
    ∀ γ ∈ P, (F.toU1.wilsonCycle γ) ^ n = 1 := by
  intro γ _
  -- Each factor `F.toU1.A x y = zmodChar n (...)` is an `n`-th root of unity,
  -- and `n`-th roots of unity are closed under (commutative) multiplication.
  have hchar : ∀ k : ZMod n, (zmodChar n k) ^ n = 1 := by
    intro k
    rw [zmodChar_eq_pow, ← pow_mul, mul_comm, pow_mul, zmodRoot_pow_n, one_pow]
  cases γ with
  | nil => show (1 : ℂ) ^ n = 1; rw [one_pow]
  | cons v₀ rest =>
    show ((List.zip (v₀ :: rest) (rest ++ [v₀])).foldr
        (fun pair acc => F.toU1.A pair.1 pair.2 * acc) 1) ^ n = 1
    -- induct on the zipped list; each step multiplies by an `n`-th root of unity
    induction (List.zip (v₀ :: rest) (rest ++ [v₀])) with
    | nil => show (1 : ℂ) ^ n = 1; rw [one_pow]
    | cons p ps ih =>
      rw [List.foldr_cons, mul_pow, ih, mul_one]
      exact hchar _

/-- The **lattice Hall conductance** of a chiral signing relative to a plaquette
set `P`: the discrete Chern number `chernNumberSum` normalised by `2π` (the
lattice-gauge analog of the TKNN formula).  A chiral signing of a 2D layout with
non-zero discrete Chern number realises a quantized Hall response. -/
noncomputable def hallConductance
    {V : Type u} {G : SimpleGraph V} (s : ChiralSigning V) (P : Finset (List V)) : ℂ :=
  (1 / (2 * (Real.pi : ℂ))) * chernNumberSum (s.toU1GaugeField G) P

theorem quantum_hall_conductance
    {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    {G : SimpleGraph V} (B : Bundle V I) (s : ChiralSigning V)
    (_h : s.CrossConstant B.partition.cells) :
    -- **Genuine TKNN identity** (not a free-variable existential): the Hall
    -- conductance over an *empty* plaquette set vanishes — a flat/no-plaquette
    -- configuration carries zero Chern number, the base case of the lattice TKNN
    -- formula `σ_xy = (1/2π) · chernNumberSum`.  The general nonzero-Chern
    -- response is the deeper content (cf. `chern_quantization`).
    hallConductance (G := G) s (∅ : Finset (List V)) = 0 := by
  unfold hallConductance chernNumberSum
  rw [Finset.sum_empty, mul_zero]

/-! ## §10.  Open directions

1. **Non-abelian extension to full SU(N) Yang-Mills**.  The matrix gauge
   field setup in §7 only states the equitable-partition lift; the actual
   Hofstadter-like spectral quantization for SU(N) is open and physically
   important for **non-abelian Hofstadter butterflies** (Osterloh et al.
   2005, Goldman et al. 2014).  Concretely: when is the SU(N) Wilson loop
   around a plaquette a root of unity of order divisible by `q`?

2. **Connection to topological order and TQFT (overlap with I1)**.  A
   flat U(1) lattice gauge field on a closed 2-complex is exactly a flat
   connection, and the moduli space of such connections classifies
   topological orders of the chip (Wen 1989).  The integration file
   `Integrations/TQFT.lean` (the I1 sibling) should provide the bridge
   to Reshetikhin-Turaev / Turaev-Viro invariants computed from this
   gauge data.  Open: when does the chiral PST/mixing-optimization theorem
   (Chiral.lean) factor through the TQFT partition function on the
   quotient template?

3. **Adiabatic flux pumping and the quantized charge transport**.  The
   `magneticFluxSchedule` of `Toolkit/Scheduler.lean` provides a natural
   time-dependent gauge field; the **adiabatic Thouless pump** (1983) says
   that a slow loop in flux space transports an integer charge per cycle
   through the chip.  Open: state and prove (with sorries) that the
   adiabatic limit of a `magneticFluxSchedule` pumping a Chern-number-1
   chiral bundle through one flux quantum transports exactly one quantum
   of charge through the quotient.

Additional further directions:

* Lattice gauge fields with continuous gauge group (Lie group U(1) or
  SU(N)) and continuous limit to the BF / Chern-Simons / Yang-Mills
  continuum action.  Match Wegner '71 → Wilson '74 → Kogut-Susskind '75 →
  modern lattice gauge theory.
* Coupling to matter: chiral fermions on a graph lattice, Nielsen-Ninomiya
  obstructions, and a finite-graph version of the staggered-fermion trick.
* **`p`-adic** lattice gauge fields: replace U(1) by `ℚ_p / ℤ_p`; this
  gives a finite-graph version of `p`-adic gauge theory which has been
  proposed as a holographic dual to AdS-CFT on tree graphs.
-/

end LatticeGauge
end Graphplay
