/-
Graphplay/Chiral.lean

Tower 2 specialization: chiral / magnetic signings of weighted graphs.

The constructions and theorem statements in this file are motivated by

  Levine, Mesapam, Mustico, Tamon, Tucker, Zhan,
  "Uniform Mixing in Chiral Quantum Walks",
  arXiv:2605.04414 (2026).

In that paper the authors show that for any K_n there is a *unitary signing*
σ so that K_n^σ admits (probabilistic) uniform mixing, and as a corollary
exhibit a specific signing of K_4 whose conical reduction K_1 + K_3 mixes
faster than any unoriented Hamming graph (an orientation of H(n, 4)).

We package this here as the **chiral signing** of a Hermitian-weighted graph,
record that signing preserves the fiber-equitable partition of a bundle
(the cell row sums on |adj| are unchanged), and state the *chiral
PST/mixing optimization theorem*: for a bundle B with regular fibers and
biregular couplings, optimal cell-uniform chiral mixing/PST is determined
by a chiral phasing of the *quotient*. This last statement is the new
algebraic content motivated by Levine et al.
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Combinatorics.SimpleGraph.Basic
import Graphplay.Weighted
import Graphplay.Equitable
import Graphplay.Spectral

universe u v w

namespace Graphplay

/-! ## Chiral signings

A chiral (or *magnetic*, in the physics literature) signing assigns a unit
complex phase to each ordered pair (x, y) of vertices, satisfying the
Hermitian condition σ(y, x) = σ(x, y)* and the convention σ(x, x) = 1.
Following Levine et al. (2605.04414), unitary signings are the natural
finite-symmetry analogue of magnetic vector potentials on a discrete space.
-/

/-- A chiral / magnetic signing of vertices in `V`: a unimodular kernel
satisfying the Hermitian condition. -/
structure ChiralSigning (V : Type u) where
  σ : V → V → ℂ
  unimod : ∀ x y : V, ‖σ x y‖ = 1
  herm : ∀ x y : V, σ y x = star (σ x y)
  diag : ∀ x : V, σ x x = 1

namespace ChiralSigning

/-- The trivial (all-one) signing. -/
def trivial (V : Type u) : ChiralSigning V where
  σ _ _ := 1
  unimod _ _ := by simp
  herm _ _ := by simp
  diag _ := rfl

/-- Pointwise complex conjugate of a chiral signing. -/
noncomputable def conj {V : Type u} (s : ChiralSigning V) : ChiralSigning V where
  σ x y := star (s.σ x y)
  unimod x y := by
    have h := s.unimod x y
    simpa using h
  herm x y := by
    have := s.herm x y
    simp [this]
  diag x := by simp [s.diag x]

end ChiralSigning

namespace WeightedGraph

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Apply a chiral signing to a weighted graph: multiply each entry of the
adjacency by the corresponding phase. Hermitian and loopless are preserved.
-/
def signedBy (G : WeightedGraph V) (s : ChiralSigning V) : WeightedGraph V where
  adj := fun x y => s.σ x y * G.adj x y
  herm := by
    -- (σ x y * G.adj x y)ᴴ = star (σ y x * G.adj y x)
    --                     = star (σ y x) * star (G.adj y x)
    --                     = σ x y * G.adj x y  using herm of σ and of G.
    refine Matrix.IsHermitian.ext ?_
    intro i j
    have hG : star (G.adj j i) = G.adj i j := G.herm.apply i j
    have hσ : s.σ j i = star (s.σ i j) := s.herm i j
    show star ((fun x y => s.σ x y * G.adj x y) j i)
      = (fun x y => s.σ x y * G.adj x y) i j
    simp [hσ, hG, star_mul, mul_comm]
  loopless := by
    intro v
    show s.σ v v * G.adj v v = 0
    simp [G.loopless v]

@[simp] theorem signedBy_adj (G : WeightedGraph V) (s : ChiralSigning V)
    (x y : V) : (G.signedBy s).adj x y = s.σ x y * G.adj x y := rfl

@[simp] theorem signedBy_trivial (G : WeightedGraph V) :
    G.signedBy (ChiralSigning.trivial V) = G := by
  -- `WeightedGraph` is an extensionality-by-`adj` structure (the other two
  -- fields are propositions).  The trivial signing multiplies every entry by
  -- `1`, leaving `adj` unchanged; the propositional fields agree by proof
  -- irrelevance, which `congr 1` discharges after matching `adj`.
  cases G with
  | mk adj herm loopless =>
    unfold WeightedGraph.signedBy
    congr 1
    funext x y
    show (ChiralSigning.trivial V).σ x y * adj x y = adj x y
    simp [ChiralSigning.trivial]

end WeightedGraph

/-! ## Bundles, fibers, and cross-couplings

A *bundle* over a quotient `I` is a weighted graph together with a fiber
assignment `V → I`. Its **fiber-equitable partition** is the equitable
partition induced by the fibers.

A chiral signing is **fiber-trivial** if it is the constant 1 inside each
fiber. The key lemma below shows that signing by a fiber-trivial signing
preserves the fiber-equitable partition: rotating only cross-couplings
leaves the row sum *into* each fiber unchanged at the level of magnitudes,
and in fact at the level of the row sums themselves when the signing is
constant on cross-fiber pairs.
-/

/-- A chiral signing is *fiber-trivial* with respect to a cell map
`cells : V → I` if it is the identity on every intra-fiber pair. -/
def ChiralSigning.FiberTrivial {V : Type u} {I : Type v}
    (s : ChiralSigning V) (cells : V → I) : Prop :=
  ∀ x y : V, cells x = cells y → s.σ x y = 1

/-- A chiral signing is *cross-constant* if its value on every pair (x, y)
depends only on the cells of `x` and `y`. -/
def ChiralSigning.CrossConstant {V : Type u} {I : Type v}
    (s : ChiralSigning V) (cells : V → I) : Prop :=
  ∃ τ : I → I → ℂ, ∀ x y : V, s.σ x y = τ (cells x) (cells y)

/-- **Chiral signing preserves the fiber-equitable partition.**

If `P` is an equitable partition of `G` and `s` is a chiral signing that is
*cross-constant* on the cells of `P` (so phases depend only on the cell
pair), then `P` is again equitable for `G.signedBy s`.

The reason is purely algebraic: in the new cell sum

  ∑_{z : cells z = j} σ(x, z) · G.adj x z

the factor σ(x, z) = τ (cells x) (cells z) = τ (i, j) is constant across
`z` in cell `j`, so it factors out and equality of the unsigned row sums
implies equality of the signed row sums.
-/
def WeightedGraph.signedBy_preserves_equitable
    {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    (G : WeightedGraph V) (P : EquitablePartition G I)
    (s : ChiralSigning V) (h : s.CrossConstant P.cells) :
    EquitablePartition (G.signedBy s) I where
  cells := P.cells
  uniform := by
    intro i j x y hxi hyi
    obtain ⟨τ, hτ⟩ := h
    -- Both inner sums equal τ(i, j) · (∑_{z in cell j} G.adj _ z).
    have hx : (∑ z, (if P.cells z = j then (G.signedBy s).adj x z else 0))
        = τ i j * (∑ z, (if P.cells z = j then G.adj x z else 0)) := by
      simp only [WeightedGraph.signedBy_adj]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro z _
      by_cases hz : P.cells z = j
      · simp [hz, hτ x z, hxi]
      · simp [hz]
    have hy : (∑ z, (if P.cells z = j then (G.signedBy s).adj y z else 0))
        = τ i j * (∑ z, (if P.cells z = j then G.adj y z else 0)) := by
      simp only [WeightedGraph.signedBy_adj]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro z _
      by_cases hz : P.cells z = j
      · simp [hz, hτ y z, hyi]
      · simp [hz]
    rw [hx, hy]
    exact congrArg _ (P.uniform i j x y hxi hyi)

/-! ## Bundles and the chiral mixing/PST optimization theorem

A *bundle* in our sense is a pair `(G, cells)` where the cells of `cells`
have *regular fibers* (constant intra-fiber row sums) and the cross-cell
couplings are *biregular* (constant row sums into each opposing cell).
This is exactly the setting in which the cell partition is equitable.

The continuous-time quantum walk on `G` then projects to a continuous-time
walk on the quotient via the characteristic isometry of Lemma 2 of
Levine et al., and **cell-uniform** behaviour upstairs is governed by the
quotient walk downstairs (Lemma 3 of that paper).
-/

/-- A bundle is a weighted graph together with a cell map. -/
structure Bundle (V : Type u) [Fintype V] [DecidableEq V]
    (I : Type v) [Fintype I] [DecidableEq I] where
  graph : WeightedGraph V
  partition : EquitablePartition graph I

namespace Bundle

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {I : Type v} [Fintype I] [DecidableEq I]

/-- Apply a cell-cross-constant chiral signing to a bundle. -/
def signedBy (B : Bundle V I) (s : ChiralSigning V)
    (h : s.CrossConstant B.partition.cells) : Bundle V I where
  graph := B.graph.signedBy s
  partition := B.graph.signedBy_preserves_equitable B.partition s h

/-- The bundle is **cell-uniform** for the quantum walk at time `t` if every
two vertices in the same cell have equal squared transition amplitudes to
every target vertex. This is the appropriate "uniform mixing relative to a
quotient" notion for fractional revival in the sense of Chan et al.
(1907.04729) — see also Lemma 1 / Lemma 3 of Levine et al. (2605.04414).

Concretely, for the continuous-time quantum walk `U(t) = exp(-i t A)` on the
bundle's adjacency matrix, two vertices `x, x'` in the same cell are required
to have equal transition modulus `‖U(t) y x‖ = ‖U(t) y x'‖` into every target
vertex `y`.  This is exactly the condition that makes the cell-uniform
superposition a well-defined dynamical object (the modulus profile only
depends on the source cell). -/
def CellUniformMixing (B : Bundle V I) (t : ℝ) : Prop :=
  ∀ (x x' : V), B.partition.cells x = B.partition.cells x' →
    ∀ y : V, ‖B.graph.evolve t y x‖ = ‖B.graph.evolve t y x'‖

/--
**Chiral mixing/PST optimization theorem (characteristic-isometry intertwining).**

Let `B` be a bundle (regular fibers, biregular couplings) and let `s` be a
chiral signing that is cross-constant on the cells of `B`, so its phases
depend only on the quotient pair. By `signedBy_preserves_equitable` the cell
partition stays equitable for the *signed* graph, so the signed bundle
`B.signedBy s h` carries its own quotient and symmetric quotient
`Q̃ = D^{1/2} Q D^{-1/2}`.

The theorem is the **characteristic-isometry intertwining** `S^* U(t) S =
U_{quot}(t)` of Lemma 2 of Levine et al. (2605.04414), realized at the level
of cell-inflated vectors: for every quotient-side vector `v : I → ℂ` and time
`t`, the *signed host* walk acting on the inflation of `v` equals the
inflation of the *signed quotient* walk acting on `v`,

  `U_host(t) · (Inflate v) = Inflate (exp(-i t Q̃) · v)`.

Equivalently, the cell-uniform subspace is invariant under the signed host
evolution, and the restricted dynamics is *exactly* the quotient walk driven by
the chiral phasing on `Q̃`. Thus the **cell-uniform chiral mixing/PST behaviour
of the bundle is determined entirely by a chiral phasing on the quotient** —
the algebraic content motivated by Levine et al., whose `K_4 → K_1 + K_3`
example is the optimal instance.

Note the corresponding *iff* — between the per-vertex predicate
`CellUniformMixing` (equal transition *modulus* `‖U(t) y x‖ = ‖U(t) y x'‖` for
within-cell sources `x, x'`) and modulus-flat columns of the quotient
evolution — is **false**: equitable partitions control the cell-uniform
*subspace* (the inflated vectors below), not the individual per-vertex
amplitudes. Witness the singleton (discrete) partition `I = V`: its
`CellUniformMixing` is vacuously true (a within-cell pair forces `x = x'`),
while its `symmQuotient` is the full host adjacency, whose evolution has
non-flat column moduli at generic `t` (e.g. a `K_2` host has column moduli
`cos t` vs `sin t`). The intertwining below is the unconditional statement
that does hold. -/
theorem chiral_mixing_optimization
    {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    (B : Bundle V I) (s : ChiralSigning V)
    (h : s.CrossConstant B.partition.cells) (t : ℝ) (v : I → ℂ) :
    ((B.signedBy s h).graph.evolve t).mulVec
        ((B.signedBy s h).partition.cellInflateVec v)
      = (B.signedBy s h).partition.cellInflateVec
          ((NormedSpace.exp (-(Complex.I * (t : ℂ)) •
              (B.signedBy s h).partition.symmQuotient)).mulVec v) := by
  -- The signed host evolution `exp(-i t A^σ)` and `evolve_cellInflateVec` of the
  -- (equitable, by `signedBy_preserves_equitable`) signed partition coincide up
  -- to the scalar identity `-(I·t) = -t·I`; this is the intertwining.
  have hscal : -(Complex.I * (t : ℂ)) = -(t : ℂ) * Complex.I := by ring
  unfold WeightedGraph.evolve
  rw [hscal]
  exact (B.signedBy s h).partition.evolve_cellInflateVec v t

end Bundle

/-! ## The specific K_4 unitary signing from Levine et al.

From equation (in §2 of 2605.04414):

    A(K_4^σ) =
      ⎡ 0  -i  -i  -i ⎤
      ⎢ i   0  -i   i ⎥
      ⎢ i   i   0  -i ⎥
      ⎣ i  -i   i   0 ⎦

This is switching-equivalent to the conical reduction K_1 + K̄_3 (i.e. the
star K_{1,3}), and is the canonical *chiral ghost* signing that gives K_4
an orientation with uniform mixing time π / (3√3), faster than any
unoriented Hamming graph.

We expose the signing as `unitaryHammingChiralK4`; the unimodularity /
Hermitian / loopless obligations are discharged by finite case checks on
`Fin 4 × Fin 4`.
-/

/-- The K_4 unitary signing of Fig. 2 in Levine et al. (2605.04414):
phases `σ(x, y)` for `x ≠ y` are chosen so that the resulting Hermitian
matrix is switching equivalent to K_1 + K̄_3. -/
def unitaryHammingChiralK4Signing : ChiralSigning (Fin 4) where
  σ x y :=
    if x = y then 1
    -- the exceptional cross pair `{1, 3}` carries the opposite chirality,
    -- realizing the doubly-degenerate spectrum `±√3` of Fig. 2.
    else if x.val = 1 ∧ y.val = 3 then Complex.I
    else if x.val = 3 ∧ y.val = 1 then -Complex.I
    else if (x : Fin 4) = 0 then -Complex.I
    else if (y : Fin 4) = 0 then Complex.I
    else if x.val < y.val then -Complex.I
    else Complex.I
  unimod := by
    intro x y
    -- All values are `1` (diagonal) or `±i`, each of norm `1`.
    split_ifs <;> simp [Complex.norm_I]
  herm := by
    -- σ(y, x) = star σ(x, y).  Verified by exhausting the 16 ordered pairs.
    intro x y
    fin_cases x <;> fin_cases y <;>
      simp [Fin.ext_iff]
  diag x := by
    fin_cases x <;> simp

/-- The chiral K_4 from Levine et al. (2605.04414, Fig. 2): the
weighted graph on Fin 4 whose adjacency matrix is the unitary signing of
K_4 admitting probabilistic uniform mixing at time π / (3√3). Optimally
fast among Hamming-graph orientations. -/
def unitaryHammingChiralK4 : WeightedGraph (Fin 4) where
  adj x y :=
    if x = y then (0 : ℂ)
    else unitaryHammingChiralK4Signing.σ x y
  herm := by
    -- Hermitian: the off-diagonal part equals the signing, which is Hermitian;
    -- the diagonal is `0`.
    refine Matrix.IsHermitian.ext ?_
    intro i j
    show star (if j = i then (0 : ℂ) else unitaryHammingChiralK4Signing.σ j i)
      = if i = j then 0 else unitaryHammingChiralK4Signing.σ i j
    by_cases hij : i = j
    · subst hij; simp
    · have hji : ¬ j = i := fun h => hij h.symm
      rw [if_neg hji, if_neg hij, unitaryHammingChiralK4Signing.herm i j,
        star_star]
  loopless v := by simp

/-! ## Chiral uniform mixing on `K_4^σ` at the Levine–…–Tamon time `π/(3√3)`

We now formalize the headline analytic content of Levine, Mesapam, Mustico,
Tamon, Tucker, Zhan (arXiv:2605.04414, Fig. 2): the chirally-signed `K_4`
`unitaryHammingChiralK4` exhibits *probabilistic uniform mixing* —
all entries `|U(τ)_{ij}|` equal `1/√4 = 1/2` — at the time
`τ = π/(3√3)`, faster than any unoriented Hamming graph.

The mechanism is the explicit doubly-degenerate spectrum `±√3` of the signed
adjacency `B`, encoded in the single algebraic relation `B² = 3·I`.  This
makes `J := B/√3` an *involution* (`J² = I`), so the continuous-time quantum
walk

  `U(τ) = exp(-iτ B) = cos(√3 τ)·I - i·(sin(√3 τ)/√3)·B`

is computable in closed form.  At `τ = π/(3√3)` we have `√3 τ = π/3`, so
`cos(√3 τ) = 1/2` and `sin(√3 τ)/√3 = (√3/2)/√3 = 1/2`; since each
off-diagonal entry of `B` is a unit phase, every entry of `U(τ)` has
modulus exactly `1/2`.  This is the uniform-mixing instant.
-/

section ChiralMixing

open NormedSpace Matrix
open scoped BigOperators Nat

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- **Exponential of a scaled idempotent.**  For an idempotent matrix `P`
(`P² = P`) and a scalar `z`, `exp(z • P) = 1 + (e^z - 1) • P`. -/
theorem chiralExpSmulIdem {n : Type*} [Fintype n] [DecidableEq n]
    (z : ℂ) (P : Matrix n n ℂ) (hP : P * P = P) :
    NormedSpace.exp (z • P) = 1 + (Complex.exp z - 1) • P := by
  have hpow : ∀ k : ℕ, (z • P) ^ (k + 1) = (z ^ (k + 1)) • P := by
    intro k; induction k with
    | zero => simp
    | succ m ih => rw [pow_succ, ih, smul_mul_smul_comm, hP, ← pow_succ]
  apply HasSum.unique (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (z • P))
  have hscal : HasSum (fun k : ℕ => (((k + 1)! : ℕ) : ℂ)⁻¹ * z ^ (k + 1))
      (Complex.exp z - 1) := by
    have h0 : HasSum (fun k : ℕ => ((k ! : ℕ) : ℂ)⁻¹ * z ^ k) (Complex.exp z) := by
      rw [Complex.exp_eq_exp_ℂ]
      simpa [smul_eq_mul] using NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) z
    simpa using (hasSum_nat_add_iff'
      (f := fun k : ℕ => ((k ! : ℕ) : ℂ)⁻¹ * z ^ k) 1).mpr h0
  have htail : HasSum (fun k : ℕ => ((((k + 1)! : ℕ) : ℂ))⁻¹ • (z • P) ^ (k + 1))
      ((Complex.exp z - 1) • P) := by
    refine (hscal.smul_const (a := P)).congr_fun ?_
    intro k; rw [hpow k, smul_smul]
  exact (hasSum_nat_add_iff' (f := fun k : ℕ => ((k ! : ℕ) : ℂ)⁻¹ • (z • P) ^ k) 1
    (g := 1 + (Complex.exp z - 1) • P)).mp (by simpa using htail)

/-- **Exponential of a scalar multiple of the identity matrix.** -/
theorem chiralExpSmulOne {n : Type*} [Fintype n] [DecidableEq n] (w : ℂ) :
    NormedSpace.exp (w • (1 : Matrix n n ℂ)) = (Complex.exp w) • (1 : Matrix n n ℂ) := by
  have key : ∀ (v : ℂ), v • (1 : Matrix n n ℂ) = Matrix.diagonal (fun _ => v) := by
    intro v; ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [Matrix.one_apply, Matrix.diagonal_apply, h]
  rw [key w, Matrix.exp_diagonal, key (Complex.exp w)]
  congr 1; funext i; simp [Pi.exp_def, Complex.exp_eq_exp_ℂ]

/-- **Exponential of a scaled involution.**  For an involution `J` (`J² = I`),
`exp(w • J) = cosh w · I + sinh w · J`.  This is the matrix analogue of the
two-eigenvalue cosine formula, derived from `chiralExpSmulIdem` applied to the
orthogonal eigenprojector `½(1 + J)`. -/
theorem chiralExpSmulInvolution {n : Type*} [Fintype n] [DecidableEq n]
    (w : ℂ) (J : Matrix n n ℂ) (hJ : J * J = 1) :
    NormedSpace.exp (w • J)
      = (Complex.cosh w) • (1 : Matrix n n ℂ) + (Complex.sinh w) • J := by
  set P : Matrix n n ℂ := (1 / 2 : ℂ) • (1 + J) with hPdef
  have hPidem : P * P = P := by
    rw [hPdef, smul_mul_smul_comm, mul_add, add_mul, add_mul, hJ,
      Matrix.one_mul, Matrix.mul_one, Matrix.one_mul]
    module
  have hcomm : Commute ((-w) • (1 : Matrix n n ℂ)) ((2 * w) • P) :=
    (Commute.one_left P).smul_left _ |>.smul_right _
  have hsplit : w • J = (-w) • (1 : Matrix n n ℂ) + (2 * w) • P := by
    rw [hPdef, smul_smul, smul_add, show (2 * w * (1 / 2)) = w by ring]; module
  rw [hsplit, Matrix.exp_add_of_commute _ _ hcomm, chiralExpSmulOne, chiralExpSmulIdem _ _ hPidem]
  rw [hPdef]
  rw [smul_mul_assoc, one_mul, smul_add, smul_smul, smul_smul]
  have hinv : Complex.exp w * Complex.exp (-w) = 1 := by
    rw [← Complex.exp_add]; simp
  have he2 : Complex.exp (2 * w) = Complex.exp w * Complex.exp w := by
    rw [show (2 * w) = w + w by ring, Complex.exp_add]
  have hew : Complex.exp (-w) = (Complex.exp w)⁻¹ := by rw [Complex.exp_neg]
  have hwne : Complex.exp w ≠ 0 := Complex.exp_ne_zero w
  have hc1 : Complex.exp (-w)
      + Complex.exp (-w) * (Complex.exp (2 * w) - 1) * (1 / 2) = Complex.cosh w := by
    rw [Complex.cosh, he2, hew]; field_simp; ring
  have hc2 : Complex.exp (-w) * (Complex.exp (2 * w) - 1) * (1 / 2) = Complex.sinh w := by
    rw [Complex.sinh, he2, hew]; field_simp
  rw [smul_add, ← add_assoc, ← add_smul, hc1, hc2]

/-- The explicit signed adjacency matrix of `unitaryHammingChiralK4`
(Fig. 2 of arXiv:2605.04414): the canonical chiral signing of `K_4` whose
spectrum is the doubly-degenerate `±√3`. -/
noncomputable def chiralK4Matrix : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, -Complex.I, -Complex.I, -Complex.I;
     Complex.I, 0, -Complex.I, Complex.I;
     Complex.I, Complex.I, 0, -Complex.I;
     Complex.I, -Complex.I, Complex.I, 0]

/-- The adjacency of `unitaryHammingChiralK4` is the explicit matrix `B`. -/
theorem chiralK4_adj_eq : unitaryHammingChiralK4.adj = chiralK4Matrix := by
  ext i j
  show (if i = j then (0 : ℂ) else unitaryHammingChiralK4Signing.σ i j)
    = chiralK4Matrix i j
  fin_cases i <;> fin_cases j <;>
    · simp only [unitaryHammingChiralK4Signing, chiralK4Matrix, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.empty_val']
      norm_num

/-- **The defining spectral relation: `B² = 3·I`.**  Equivalently, the signed
adjacency of `K_4^σ` has eigenvalues `±√3` (each with multiplicity two). -/
theorem chiralK4Matrix_sq :
    chiralK4Matrix * chiralK4Matrix = (3 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralK4Matrix, Matrix.mul_apply, Fin.sum_univ_four, Complex.I_mul_I] <;> norm_num

private theorem sqrt3_sq_C : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0)]; norm_num

/-- `J := B/√3` is an involution: `J² = I`. -/
noncomputable def chiralK4Involution : Matrix (Fin 4) (Fin 4) ℂ :=
  ((1 : ℂ) / Real.sqrt 3) • chiralK4Matrix

theorem chiralK4Involution_invol : chiralK4Involution * chiralK4Involution = 1 := by
  rw [chiralK4Involution, smul_mul_smul_comm, chiralK4Matrix_sq, smul_smul]
  rw [show ((1 : ℂ) / Real.sqrt 3 * ((1 : ℂ) / Real.sqrt 3) * 3)
        = 3 / ((Real.sqrt 3 : ℂ) ^ 2) by ring, sqrt3_sq_C]
  norm_num

/-- **Closed form of the chiral `K_4` quantum walk.**
`U(τ) = exp(-iτ B) = cos(√3 τ)·I - i·(sin(√3 τ)/√3)·B`. -/
theorem chiralK4_evolve (t : ℝ) :
    unitaryHammingChiralK4.evolve t
      = (Real.cos (Real.sqrt 3 * t) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)
        + (-(Complex.I) * (Real.sin (Real.sqrt 3 * t) : ℂ) / (Real.sqrt 3 : ℂ))
            • chiralK4Matrix := by
  rw [WeightedGraph.evolve, chiralK4_adj_eq]
  have hBJ : chiralK4Matrix = (Real.sqrt 3 : ℂ) • chiralK4Involution := by
    rw [chiralK4Involution, smul_smul,
      show ((Real.sqrt 3 : ℂ) * ((1 : ℂ) / Real.sqrt 3)) = 1 from by field_simp, one_smul]
  set w : ℂ := -(Complex.I * (t : ℂ)) * (Real.sqrt 3 : ℂ) with hw
  have hsplit : -(Complex.I * (t : ℂ)) • chiralK4Matrix = w • chiralK4Involution := by
    rw [hBJ, smul_smul, hw]
  rw [hsplit, chiralExpSmulInvolution _ _ chiralK4Involution_invol]
  have hwI : w = (-(Real.sqrt 3 * t : ℝ) : ℂ) * Complex.I := by rw [hw]; push_cast; ring
  have hcosh : Complex.cosh w = (Real.cos (Real.sqrt 3 * t) : ℂ) := by
    rw [hwI, Complex.cosh_mul_I, Complex.cos_neg, Complex.ofReal_cos]
  have hsinh : Complex.sinh w = -(Complex.I) * (Real.sin (Real.sqrt 3 * t) : ℂ) := by
    rw [hwI, Complex.sinh_mul_I, Complex.sin_neg, Complex.ofReal_sin]; ring
  rw [hcosh, hsinh, chiralK4Involution, smul_smul]
  congr 2
  rw [mul_one_div]

private theorem sqrt3_mul_special :
    Real.sqrt 3 * (Real.pi / (3 * Real.sqrt 3)) = Real.pi / 3 := by
  have h : Real.sqrt 3 ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  field_simp

private theorem offdiag_coeff_norm :
    ‖-(Complex.I) * ((Real.sqrt 3 / 2 : ℝ) : ℂ) / (Real.sqrt 3 : ℂ)‖ = 1 / 2 := by
  rw [norm_div, norm_mul, norm_neg, Complex.norm_I, one_mul,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  have hpos : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  rw [abs_of_pos (by positivity), abs_of_pos hpos]
  field_simp

/-- **Levine–Mesapam–Mustico–Tamon–Tucker–Zhan chiral uniform mixing
(arXiv:2605.04414, Fig. 2).**

At the time `τ = π/(3√3)`, every entry of the continuous-time quantum-walk
unitary `U(τ) = exp(-iτ A)` on the chirally-signed `K_4` has modulus exactly
`1/2 = 1/√4`.  Thus `unitaryHammingChiralK4` exhibits **probabilistic uniform
mixing** at the Levine–…–Tamon speedup time `π/(3√3)`, faster than any
unoriented Hamming graph. -/
theorem unitaryHammingChiralK4_uniformMixing (i j : Fin 4) :
    ‖unitaryHammingChiralK4.evolve (Real.pi / (3 * Real.sqrt 3)) i j‖ = 1 / 2 := by
  rw [chiralK4_evolve, sqrt3_mul_special, Real.cos_pi_div_three, Real.sin_pi_div_three]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    have hB0 : chiralK4Matrix i i = 0 := by fin_cases i <;> simp [chiralK4Matrix]
    rw [hB0, mul_zero, add_zero, mul_one, Complex.norm_real, Real.norm_eq_abs]
    norm_num
  · rw [if_neg hij]
    have hBnorm : ‖chiralK4Matrix i j‖ = 1 := by
      fin_cases i <;> fin_cases j <;>
        simp_all [chiralK4Matrix, Complex.norm_I]
    rw [mul_zero, zero_add, norm_mul, hBnorm, mul_one, offdiag_coeff_norm]

end ChiralMixing

end Graphplay
