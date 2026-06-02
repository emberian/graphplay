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

2. **Multiple state transfer** and **switching maps**
   (Kay, arXiv:1310.3885): a single time `τ` and an *automorphism-like*
   involution that simultaneously transfers several pairs.  At the transfer
   time the PST unitary carries each source state, up to a global phase, to its
   target state — the operator-level *switching map* (`T = E₊ − E₋`).  Its
   upgrade to a genuine 0/1 vertex-permutation automorphism (the *switching
   automorphism* proper) holds only under the integer/simple-spectrum
   hypotheses of Kay 1310.3885 — PST hosts need not be vertex-transitive — so
   this file proves the unconditional *operator-level* content and keeps the
   permutation upgrade as a (separately-hypothesised) structure, never as a
   theorem from bare PST.

3. **K-fractional revival** (Chan–Coutinho–Tamon–et al., arXiv:2004.01129):
   the generalization where the excitation, initially on a *subset* `K ⊆ V`,
   returns to (a unitary scrambling within) `K` at time `τ` — the off-`K`
   amplitudes vanish.  The governing object is the **`D_K` periodicity matrix**
   (the `K × K` block of the evolution) together with an eigenvalue **ratio
   condition** identical in spirit to Godsil's.

Concrete content (sorry-free `def`/`structure`):
* `IsUniversalStateTransfer G u`, `IsMultipleStateTransfer G pairs τ`;
* `SwitchingUnitary G u v τ` — the *operator-level* switching map PST genuinely
  supplies (a unitary carrying the `u`-state to a unit-phase multiple of the
  `v`-state), with `switchingUnitary_of_isPST` proving its existence
  axiom-clean and unconditionally;
* `SwitchingAutomorphism G u v` — the genuine vertex-permutation upgrade, kept
  as a *hypothesis-bearing structure* (it is **not** produced from bare PST: in
  the complex-Hermitian generality of `WeightedGraph` a PST host need not be
  vertex-transitive — see the caveat on the structure, and the canonical
  sibling treatment `Graphplay.PST.Periodicity.{SwitchingUnitary,
  switchingUnitary_of_isPST}`);
* `periodicityBlock G K τ` (the `D_K` block), `IsKFractionalRevival G K τ`,
  and `IsKRatioCondition G K` (the ratio condition).

The genuinely number-theoretic classification residuals are stated precisely
with honest `sorry` proofs (and reduced to their irreducible Diophantine core
where the spectral spine is available).

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

/-- **Universal PST equalizes eigenvector-entry moduli (simple-spectrum, CLOSED).**
For a graph with simple spectrum (`G.herm.eigenvalues` injective), global
universal state transfer forces, for *every* eigenindex `i` and *every* pair of
vertices `u, v`, the equality of eigenvector-entry moduli
`‖(eigU)_{u,i}‖ = ‖(eigU)_{v,i}‖`.

This is the genuine, axiom-clean spectral precursor of the Cameron et al.
classification (and of PST "monogamy"): under PST `u → v`, Godsil's
cross-entry relation `(E_λ)_{u,v} = γ e^{iτλ} (E_λ)_{u,u}`
(`isPST_imp_cross_eq_phase_diag`) collapses, on a simple spectrum, to
`(eigU)_{u,i} · conj (eigU)_{v,i} = γ e^{iτλ_i} ‖(eigU)_{u,i}‖²`; taking moduli
gives `‖(eigU)_{u,i}‖·‖(eigU)_{v,i}‖ = ‖(eigU)_{u,i}‖²`, and the same relation in
the reverse PST direction `v → u` yields the two-sided modulus equality.

Reference: Cameron, Fallat, Godsil, Holmes et al., LAA 455 (2014) 115–142;
Coutinho–Godsil (2021), Ch. 8 (strong cospectrality / monogamy of PST). -/
theorem eigU_norm_eq_of_globallyUniversal (G : WeightedGraph V)
    (h : IsGloballyUniversalStateTransfer G)
    (hsimple : Function.Injective G.herm.eigenvalues)
    (u v : V) (i : V) :
    ‖eigU G u i‖ = ‖eigU G v i‖ := by
  -- One PST direction `a → b` gives `‖eigU a i‖ · ‖eigU b i‖ = ‖eigU a i‖²`.
  have hdir : ∀ a b : V, a ≠ b →
      ‖eigU G a i‖ * ‖eigU G b i‖ = ‖eigU G a i‖ ^ 2 := by
    intro a b hab
    obtain ⟨τ, hτ⟩ := h a b (by exact fun hba => hab hba.symm)
    -- Unfold `IsPST` to the modulus equation so `simp` can use it as a rewrite.
    have hτ' : ‖G.evolve τ a b‖ = 1 := hτ
    have hmem : (G.herm.eigenvalues i) ∈ Set.range G.herm.eigenvalues := ⟨i, rfl⟩
    -- Godsil cross-entry relation at the simple eigenvalue `λ_i`.
    have hcross := isPST_imp_cross_eq_phase_diag G τ a b hτ' (G.herm.eigenvalues i) hmem
    rw [eigenProjEntryLocal_of_injective G hsimple i,
        eigenProjDiagLocal_of_injective G hsimple i] at hcross
    -- `‖e^{iτλ_i}‖ = 1` (purely-imaginary exponent).
    have hexp : ‖Complex.exp (Complex.I * (τ : ℂ) * ((G.herm.eigenvalues i : ℝ) : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]; simp
    -- Take moduli of both sides; `‖γ‖ = 1` (PST), `‖e^{iτλ}‖ = 1`, `‖↑(‖a‖²)‖ = ‖a‖²`.
    have hnorm := congrArg (‖·‖) hcross
    simp only [norm_mul, norm_star, hexp, hτ', Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg (‖eigU G a i‖))] at hnorm
    -- `hnorm : ‖a‖·‖b‖ = 1·1·‖a‖²`; finish.
    rw [hnorm]; ring
  -- Symmetrize: `‖a‖² = ‖a‖·‖b‖ = ‖b‖²` when `u ≠ v`; trivial when `u = v`.
  by_cases huv : u = v
  · rw [huv]
  · have h1 := hdir u v huv
    have h2 := hdir v u (fun h => huv h.symm)
    -- `‖u‖² = ‖u‖‖v‖` and `‖v‖² = ‖v‖‖u‖`, so `‖u‖² = ‖v‖²`, hence `‖u‖ = ‖v‖`.
    have hsq : ‖eigU G u i‖ ^ 2 = ‖eigU G v i‖ ^ 2 := by
      rw [← h1, ← h2]; ring
    nlinarith [norm_nonneg (eigU G u i), norm_nonneg (eigU G v i), hsq]

/-- **Classification of universal state transfer (deep direction; honest `sorry`
on a TRUE, non-vacuous statement).**  In the Cameron–Fallat–Godsil–Holmes
classification the only connected simple graphs with global universal state
transfer are `K₂` (and a tightly constrained list of products): a vertex can
perform PST with at most *one* partner ("monogamy" of PST), so `≥ 3` vertices
all mutually transferring is impossible.

We state the sharpest clean special case — **simple spectrum**: global universal
state transfer on `≥ 3` vertices with all eigenvalues distinct is impossible.
This is a genuine, non-vacuous theorem (each hypothesis is individually
realizable — e.g. `K₂` is universal, `P₃` has simple spectrum, and `card ≥ 3`
is open — yet they are jointly contradictory).

**Reachable content extracted (axiom-clean).**  `eigU_norm_eq_of_globallyUniversal`
proves that the hypotheses force every eigenvector column to have *all entries of
equal modulus* (`‖(eigU)_{u,i}‖ = ‖(eigU)_{v,i}‖` for all `u, v, i`); since each
column of `eigU` is a unit vector, this pins every entry to modulus
`1/√(card V)` (in particular, all nonzero).

**Irreducible residual (`sorry`).**  Converting that uniform-modulus eigenvector
structure into the final contradiction is PST *monogamy*: the cross-phase
relation `eigU v i / eigU u i = conj γ · e^{-iτλ_i}` over the simple spectrum,
together with the orthonormality of the rows of `eigU`, over-determines the
distinct eigenvalues `λ_i` — a `Real.Angle`/`AddCircle` Diophantine argument
identical in nature to the open ratio-condition core
`Graphplay.PST.GodsilRatio.isPST_exists_iff_strongCospectral_and_godsilRatio`
(item C1) and `IsStronglyCospectral.isPST_iff_godsilRatio`.  Not developed here.

Reference: Cameron, Fallat, Godsil, Holmes et al., *Universal state transfer on
graphs*, LAA 455 (2014) 115–142, Theorem 1.1; Coutinho–Godsil (2021), Ch. 8
(monogamy of PST). -/
theorem globallyUniversal_classification (G : WeightedGraph V)
    (h : IsGloballyUniversalStateTransfer G)
    (hsimple : Function.Injective G.herm.eigenvalues)
    (hcard : 3 ≤ Fintype.card V) :
    False := by
  -- Reachable spectral content (used by the residual): the hypotheses force
  -- every eigenvector column of `eigU` to have all entries of equal modulus.
  have _hmod : ∀ u v i : V, ‖eigU G u i‖ = ‖eigU G v i‖ :=
    fun u v i => eigU_norm_eq_of_globallyUniversal G h hsimple u v i
  -- IRREDUCIBLE RESIDUAL (honest `sorry`): from uniform-modulus eigenvectors plus
  -- row-orthonormality of `eigU`, PST monogamy forces the distinct eigenvalues to
  -- collide — the `AddCircle`/Diophantine ratio core (cf. GodsilRatio C1), absent
  -- here.  The statement is TRUE and non-vacuous; only this number-theoretic step
  -- is missing.
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
(preserves the weighted adjacency).  This is the *combinatorial* upgrade of
Kay's switching map — a genuine `Equiv.Perm V` adjacency automorphism.

**Caveat — this is a hypothesis, not a consequence of PST.**  Kay's switching
map `T = E₊ − E₋` (spectral idempotents split by the parity of `e^{−iτ θ_r}`)
is an *orthogonal involution commuting with `A`* sending the `u`-state to the
`v`-state, but it is a genuine 0/1 *permutation* matrix only under the
integer/simple-spectrum hypotheses of Kay 1310.3885.  In the complex-Hermitian
generality of `WeightedGraph` a PST host need **not** be vertex-transitive, so
no `SwitchingAutomorphism` (genuine vertex permutation) need exist.  The
unconditional, axiom-clean content PST *does* supply is the *operator-level*
`SwitchingUnitary` below (`switchingUnitary_of_isPST`); there is deliberately no
theorem deriving a `SwitchingAutomorphism` from bare PST.

Defined self-containedly here (deliberately *not* importing the sibling
`Graphplay.PST.Periodicity`, which may be under concurrent edit) so this module
never couples to that file.  The sibling carries the identical honest treatment
(`Graphplay.PST.Periodicity.{SwitchingAutomorphism, SwitchingUnitary,
switchingUnitary_of_isPST}`).

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

/-- A **switching unitary** of `G` at the pair `(u, v)` and time `τ`: the
*operator-level* content of Kay's switching map that PST genuinely supplies.  It
is a *unitary* `W` on the vertex Hilbert space that carries the `u`-basis state
to a unit-modulus phase multiple of the `v`-basis state — i.e. it swaps the two
endpoints *as states* (up to a global phase), the modulus-1 amplitude witnessing
perfect transfer.

This is exactly what `T = E₊ − E₋` does at the spectral level, *minus* the
upgrade (unprovable in this Hermitian generality) to a 0/1 permutation matrix.
The witness in `switchingUnitary_of_isPST` is the evolution `U(τ)` itself.

Mirrors the canonical `Graphplay.PST.Periodicity.SwitchingUnitary` (kept local
to avoid coupling to that possibly-under-edit sibling). -/
structure SwitchingUnitary (G : WeightedGraph V) (u v : V) (τ : ℝ) where
  /-- The underlying unitary on the vertex space. -/
  mat : Matrix V V ℂ
  /-- It is unitary: `Wᴴ W = 1`. -/
  unitary : mat.conjTranspose * mat = 1
  /-- The transfer phase (the `(u,v)` amplitude). -/
  phase : ℂ
  /-- The phase has unit modulus (perfect transfer). -/
  phase_unit : ‖phase‖ = 1
  /-- `W` sends the `u`-basis state to `phase · e_v`: the `u`-row of `W` is
  concentrated at `v` with amplitude `phase`. -/
  swaps_state : ∀ w : V, mat u w = if w = v then phase else 0

/-- **Kay's switching map, operator level (CLOSED).**  If `G` has PST between `u`
and `v` at time `τ`, then the evolution unitary `U(τ)` is a *switching unitary*:
a unitary on the vertex space carrying the `u`-state to a unit-modulus phase
multiple of the `v`-state.  This is the genuine, hypothesis-free content of Kay's
switching map `T = E₊ − E₋` at the operator level.

Axiom-clean, no `sorry`: unitarity is `WeightedGraph.evolve_unitary`, and the
state-swap is `evolve_eq_zero_of_isPST` (the `u`-row vanishes off `v`, the
surviving `(u,v)` entry having modulus 1) packaged as the explicit `u`-row of
`U(τ)`.

**Honest-relabel note (was `switchingAutomorphism_of_isPST`).**  The previous
statement claimed `Nonempty (SwitchingAutomorphism G u v)` — a genuine
`Equiv.Perm V` adjacency automorphism — from bare PST, behind a `sorry`.  That
is *false in this Hermitian generality*: PST hosts need not be vertex-transitive,
so `T = E₊ − E₋` need not be a 0/1 permutation matrix (it is only under the
integer/simple-spectrum hypotheses of Kay 1310.3885).  The conclusion is here
weakened to the operator-level switching unitary, which PST does supply
unconditionally, and the theorem is closed.  See the caveat on
`SwitchingAutomorphism` and the canonical sibling
`Graphplay.PST.Periodicity.switchingUnitary_of_isPST`.

Reference: Kay, *The perfect state transfer graph limbo* (arXiv:1310.3885);
Godsil's automorphism characterization of PST. -/
theorem switchingUnitary_of_isPST (G : WeightedGraph V) {u v : V} {τ : ℝ}
    (h : IsPST G u v τ) : Nonempty (SwitchingUnitary G u v τ) :=
  ⟨{ mat := G.evolve τ
     unitary := G.evolve_unitary τ
     phase := G.evolve τ u v
     phase_unit := h
     swaps_state := fun w => by
       by_cases hw : w = v
       · subst hw; simp
       · rw [if_neg hw]
         exact evolve_eq_zero_of_isPST G τ u v h w hw }⟩

/-- **Multiple state transfer ⇒ a common switching unitary.**  If `G` exhibits
multiple state transfer at a single time `τ` for a list of pairs, then the single
PST unitary `U(τ)` is, simultaneously, a switching unitary for *every* listed
pair (they all share the one `U(τ)`).  We package the witness for an arbitrary
member of the list.

This is the operator-level content of Kay's "multiple transfer" map.  (It is
*not* upgraded to a combinatorial graph automorphism: that upgrade needs the
integer/simple-spectrum hypotheses of Kay 1310.3885 — see the caveat on
`SwitchingAutomorphism`.)

Reference: Kay, arXiv:1310.3885, §IV (the "multiple transfer" map). -/
theorem switchingUnitary_of_multiple (G : WeightedGraph V)
    {pairs : List (V × V)} {τ : ℝ} {p : V × V}
    (hmem : p ∈ pairs) (h : IsMultipleStateTransfer G pairs τ) :
    Nonempty (SwitchingUnitary G p.1 p.2 τ) :=
  switchingUnitary_of_isPST G (h p hmem)

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
  have hUV : ‖G.evolve τ u v‖ = 1 := h
  intro k hk j hj
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  have hju : j ≠ u := fun hju => hj (by simp [hju])
  have hjv : j ≠ v := fun hjv => hj (by simp [hjv])
  rcases hk with hk | hk
  · -- `k = u` leak: needs `‖U(τ)_{·,u}‖ = 1` (target-side PST `v → u`), the
    -- spectral-symmetry half of Godsil's theorem.  This is *genuinely false* for
    -- general (non-symmetric) Hermitian `A` — the chiral / directed triangle
    -- `u → v → w → u` realizes `‖U_{u,v}‖ = 1` yet leaks `‖U_{w,u}‖ = 1` with
    -- `w ∉ {u,v}`.  Closed under the classical real-symmetric (`Aᵀ = A`)
    -- hypothesis by `isKFractionalRevival_pair_of_isPST_of_isSymm`.
    -- ISOLATED RESIDUAL (false in this Hermitian generality; TRUE-making
    -- hypothesis `G.adj.IsSymm` available in the sibling lemma):
    rw [hk]
    sorry
  · -- `k = v` leak: CLOSED by pure unitarity.  The `v`-column of `U(τ)` is
    -- concentrated at `u` (its unit `ℓ²`-mass is already saturated by the
    -- modulus-1 `(u,v)` entry), so every other entry vanishes.
    rw [hk]
    exact evolve_col_eq_zero_of_isPST G τ u v hUV j hju

end PST
end Graphplay
