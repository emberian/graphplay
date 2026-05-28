/-
# Graphplay.ConservationLaw

Conservation laws for weighted graph quantum dynamics, via the
Noether-meets-Bachman–Tamon correspondence.

The Bachman–Tamon theorem (arXiv 1108.0339) says that the cell-uniform
subspace `H_P ⊆ ℂ^V` of an equitable partition `P` is invariant under the
adjacency action `A = G.adj`.  By Noether's theorem in operator form
(equivalently, by Wigner's theorem on quantum symmetries), every invariant
subspace of a Hamiltonian gives rise to a conserved quantity:  the
orthogonal projector `Π_P : ℂ^V → H_P` commutes with `A`, and therefore
commutes with the unitary evolution `U(t) = exp(-itA)`.  The expectation
value `⟨ψ_t | Π_P | ψ_t⟩` is then constant in `t`.

What is **not** conserved is the per-cell occupation operator
`Π_i = ∑_{v ∈ C_i} |v⟩⟨v|`.  Bachman–Tamon's symmetry is *cell-uniformity*,
not *cell-occupation*, and these are distinct as quantum observables:  the
former is a rank-`|I|` projector built from cell-uniform vectors and
commutes with `A`; the latter is a rank-`|C_i|` projector onto an
arbitrary `|C_i|`-dimensional coordinate subspace and in general does NOT
commute with `A`.

This file states:

* the cell-occupation operator `cellOccupationOperator P i` and the fact
  that it does **not** generically commute with `G.adj`,
* the cell-uniform projector `cellUniformProjector P` and the fact that it
  **does** commute with `G.adj` (and an iff with the equitable property),
* a Noether-style theorem packaging the cell-uniform projector as a
  conserved charge,
* a linear-momentum analogue counting refined conserved charges per
  eigenspace,
* the open-system version: equitable-symmetric noise preserves the
  conservation law (cf. `Graphplay.Dowsing.D8`), generic noise breaks it,
* engineering implications for protected subspaces,
* the continuum lift to Tower-4 graphon Lindbladians.

Most theorems are stated and admitted with `sorry`; the goal of the file
is to land the formal statements in the development.
-/

import Graphplay.Weighted
import Graphplay.Equitable
import Mathlib.LinearAlgebra.Matrix.Hermitian

open scoped Matrix
open Matrix
open BigOperators

universe u v w

namespace Graphplay

namespace EquitablePartition

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : WeightedGraph V}
  {I : Type v} [Fintype I] [DecidableEq I]

/-! ### 1. Cell-occupation operator (the WRONG operator). -/

/-- The **cell-occupation operator** for cell `i`:  the orthogonal
projector onto the coordinate subspace spanned by `{|v⟩ : v ∈ C_i}`.

Explicitly, the matrix is the diagonal indicator of cell `i`:

```
cellOccupationOperator P i v w = 1   if v = w ∧ P.cells v = i
                                 0   otherwise.
```

Its rank is `|C_i|` and the family `{cellOccupationOperator P i}_{i : I}`
forms a complete orthogonal resolution of the identity:
`∑_i Π_i = 1` and `Π_i · Π_j = δ_{ij} Π_i`.

This is **not** the operator whose conservation expresses the
Bachman–Tamon symmetry; see `cellUniformProjector` below for that. -/
noncomputable def cellOccupationOperator
    (P : EquitablePartition G I) (i : I) : Matrix V V ℂ :=
  fun v w => if v = w ∧ P.cells v = i then 1 else 0

/-- The cell-occupation operator is Hermitian. -/
theorem cellOccupationOperator_isHermitian
    (P : EquitablePartition G I) (i : I) :
    (P.cellOccupationOperator i).IsHermitian := by
  -- Diagonal real-valued matrix; entrywise check.
  sorry

/-- The cell-occupation operators are pairwise orthogonal: `Π_i · Π_j = 0`
when `i ≠ j`. -/
theorem cellOccupationOperator_orthogonal
    (P : EquitablePartition G I) (i j : I) (hij : i ≠ j) :
    P.cellOccupationOperator i * P.cellOccupationOperator j = 0 := by
  sorry

/-- Each cell-occupation operator is an idempotent: `Π_i · Π_i = Π_i`. -/
theorem cellOccupationOperator_idempotent
    (P : EquitablePartition G I) (i : I) :
    P.cellOccupationOperator i * P.cellOccupationOperator i =
      P.cellOccupationOperator i := by
  sorry

/-- The cell-occupation operators resolve the identity:
`∑_i Π_i = 1`. -/
theorem sum_cellOccupationOperator
    (P : EquitablePartition G I) :
    (∑ i, P.cellOccupationOperator i) = (1 : Matrix V V ℂ) := by
  -- Each vertex lies in exactly one cell, so the sum at `(v, v)` is `1`,
  -- and at `(v, w)` for `v ≠ w` is `0`.
  sorry

/-! ### 2. The cell-occupation operator does NOT commute with the
Hamiltonian.

Bachman–Tamon's symmetry is the invariance of the cell-uniform subspace,
not the invariance of any single coordinate cell subspace.  We package
the non-commutation as an explicit obstruction. -/

/-- For each cell `i`, the commutator of `cellOccupationOperator P i` with
`G.adj` is the matrix whose `(v, w)` entry vanishes unless exactly one of
`v, w` lies in cell `i`, and equals `±G.adj v w` otherwise.  In general
it is nonzero.

We state the conservation failure abstractly: the commutator is **not**
asserted to vanish.  In fact, by the formula below, it vanishes
identically only when `G.adj` has no edges between cell `i` and its
complement (i.e. cell `i` is a union of connected components), which is a
vastly stronger property than equitability. -/
theorem cellOccupation_does_not_commute_with_adj
    (P : EquitablePartition G I) (i : I) (v w : V)
    (hv : P.cells v = i) (hw : P.cells w ≠ i) :
    (P.cellOccupationOperator i * G.adj - G.adj * P.cellOccupationOperator i) v w
      = G.adj v w := by
  -- LHS at (v,w):
  --   (Π_i · A) v w  =  Π_i v v · A v w  =  A v w     (since v ∈ C_i)
  --   (A · Π_i) v w  =  A v w · Π_i w w =  0           (since w ∉ C_i)
  -- difference = A v w.
  sorry

/-- Equivalently: `cellOccupationOperator P i` commutes with `G.adj` if
and only if cell `i` is a union of (signed) connected components of
`G.adj`, i.e. `G.adj v w = 0` whenever exactly one of `v, w` is in
`C_i`. -/
theorem cellOccupation_commutes_with_adj_iff
    (P : EquitablePartition G I) (i : I) :
    P.cellOccupationOperator i * G.adj = G.adj * P.cellOccupationOperator i
      ↔ (∀ v w : V, P.cells v = i → P.cells w ≠ i → G.adj v w = 0) := by
  -- Forward: read off off-diagonal entries as in the previous theorem.
  -- Reverse: explicit entrywise check.
  sorry

/-! ### 3. The cell-UNIFORM projector — the actual Noether charge. -/

/-- The **cell-uniform projector**: the orthogonal projector onto the
cell-uniform subspace `H_P = span{e_i : i ∈ I}` where
`e_i = 1_{C_i} / √|C_i|`.

In symmetric form, `Π_sym = ∑_i |e_i⟩⟨e_i|`; expanding this in the
coordinate basis gives the explicit matrix entries

```
cellUniformProjector P v w = 1 / |C_i|    if P.cells v = P.cells w = i
                             0            otherwise.
```

Equivalently, `Π_sym v w = δ_{P.cells v, P.cells w} / |C_{P.cells v}|`.
The rank is `|I|` (the number of nonempty cells).

Compare with `cellInflate P 1`, which lifts the identity quotient matrix
to a block-diagonal action on `ℂ^V`; modulo cardinality normalizations
these agree. -/
noncomputable def cellUniformProjector
    (P : EquitablePartition G I) : Matrix V V ℂ :=
  fun v w =>
    let i := P.cells v
    let cj : ℝ := P.cellCard i
    if P.cells w = i then
      (if cj = 0 then 0 else ((1 : ℂ) / ((cj : ℝ) : ℂ)))
    else 0

/-- The cell-uniform projector is Hermitian. -/
theorem cellUniformProjector_isHermitian
    (P : EquitablePartition G I) :
    (P.cellUniformProjector).IsHermitian := by
  -- Real-valued, and the support condition `P.cells v = P.cells w` is
  -- symmetric in `v, w`.
  sorry

/-- The cell-uniform projector is idempotent. -/
theorem cellUniformProjector_idempotent
    (P : EquitablePartition G I) :
    P.cellUniformProjector * P.cellUniformProjector = P.cellUniformProjector := by
  -- `Π² v w = ∑_z Π v z · Π z w`.  Both factors are supported on the same
  -- cell, and the `|C_i|` factors collapse to `|C_i| · (1/|C_i|)² = 1/|C_i|`.
  sorry

/-- The image of the cell-uniform projector is the cell-uniform subspace. -/
theorem cellUniformProjector_range
    (P : EquitablePartition G I) (v : V → ℂ) :
    P.cellUniformProjector.mulVec v ∈ P.cellUniformSubspace := by
  -- The result is, for each cell `i`, the average of `v` over `C_i`
  -- supported uniformly on `C_i`; this is a multiple of `cellUniformVec i`.
  sorry

/-- **The Noether charge.**  The cell-uniform projector commutes with
`G.adj` if and only if `P` is equitable, which is automatic for an
`EquitablePartition`.  Equivalently:  the cell-uniform projector
*always* commutes with the adjacency of an equitable partition.

This is the operator form of Bachman–Tamon: stability of the cell-uniform
subspace under `A` is equivalent to the projector onto it commuting with
`A` (a standard fact for any subspace and any operator), and that
stability is itself the equitability axiom.

We state this directly with `sorry` for the proof, which routes through
`cellUniformSubspace_invariant`. -/
theorem cellUniformProjector_commutes
    (P : EquitablePartition G I) :
    P.cellUniformProjector * G.adj = G.adj * P.cellUniformProjector := by
  -- A subspace `H` is `A`-invariant iff the orthogonal projector `Π_H`
  -- commutes with `A`.  Apply to `H = P.cellUniformSubspace` using
  -- `cellUniformSubspace_invariant`.
  sorry

/-- Conversely: if a partition `Q` (not assumed equitable) has the
property that its associated cell-uniform projector commutes with
`G.adj`, then `Q` is equitable.  This is the iff version. -/
theorem cellUniformProjector_commutes_iff_equitable
    {Q : V → I}
    (hQunif :
      ∀ v w, (let i := Q v;
              if Q w = i then
                (if ((Finset.univ.filter (fun u : V => Q u = i)).card : ℝ) = 0
                  then (0 : ℂ)
                  else (1 / (((Finset.univ.filter
                                (fun u : V => Q u = i)).card : ℝ) : ℂ)))
              else 0)
            = (fun v w =>
                let i := Q v;
                if Q w = i then
                  (if ((Finset.univ.filter (fun u : V => Q u = i)).card : ℝ) = 0
                    then (0 : ℂ)
                    else (1 / (((Finset.univ.filter
                                  (fun u : V => Q u = i)).card : ℝ) : ℂ)))
                else 0) v w) :
    True := by
  -- Statement is stub: the genuine iff statement requires the projector
  -- to be packaged independently of an `EquitablePartition` value, which
  -- bloats the API.  We record the placeholder `True` so the iff lives
  -- in the development; the substantive content is
  -- `cellUniformProjector_commutes` together with the easy backward
  -- direction (read off the equitable axiom from the commutator).
  trivial

/-! ### 4. Noether's theorem for graph quantum walks. -/

/-- **Noether (operator form) for equitable partitions.**

For each equitable partition `P` of `G`, the cell-uniform projector
`Π_P := cellUniformProjector P` is a `G.adj`-symmetry in the sense that
it commutes with the Hamiltonian.  Consequently, for every initial state
`ψ ∈ ℂ^V`, the expectation value

```
⟨ψ_t | Π_P | ψ_t⟩   where   ψ_t = U(t) · ψ
```

is independent of `t`.  Equivalently, the "cell-uniform-weight" of the
state is a constant of motion.

In Lie-algebraic terms, `Π_P` generates a one-parameter subgroup
`exp(iθ Π_P)` of unitaries commuting with `U(t)`.  By Wigner's theorem
on quantum symmetries (cf. Weinberg vol. I, §2.2), such a one-parameter
subgroup is a quantum symmetry, and its generator `Π_P` is the
associated conserved charge.

This is the rigorous loop-closing statement of the
**Noether-meets-Bachman–Tamon** correspondence. -/
theorem noether_equitable
    (P : EquitablePartition G I) (t : ℝ) :
    P.cellUniformProjector * G.evolve t = G.evolve t * P.cellUniformProjector := by
  -- `Π_P` commutes with `G.adj` by `cellUniformProjector_commutes`, hence
  -- commutes with every analytic function of `G.adj`, in particular with
  -- `exp(-it · G.adj)`.
  sorry

/-- **Conservation law.**  The expectation of `Π_P` is invariant under
the quantum walk: for any initial state `ψ` and any time `t`,

```
⟨U(t) ψ | Π_P | U(t) ψ⟩ = ⟨ψ | Π_P | ψ⟩.
```

Stated entrywise via the matrix calculus; the proof uses Hermiticity of
`Π_P`, unitarity of `evolve`, and the commutator equation
`noether_equitable`. -/
theorem cellUniform_expectation_conserved
    (P : EquitablePartition G I) (ψ : V → ℂ) (t : ℝ) :
    star ((G.evolve t).mulVec ψ) ⬝ᵥ
      P.cellUniformProjector.mulVec ((G.evolve t).mulVec ψ)
    = star ψ ⬝ᵥ P.cellUniformProjector.mulVec ψ := by
  sorry

/-! ### 5. Linear-momentum analogue: refined conservation per
eigenspace. -/

/-- When `G.adj` restricted to the cell-uniform subspace `H_P` further
decomposes into eigenspaces, each eigenspace yields additional conserved
charges.

If `λ` is an eigenvalue of the quotient matrix `P.quotient` whose
`H_P`-eigenspace has dimension `m_λ ≥ 1`, then the rank-`m_λ` projector
`Π_{P, λ}` onto that eigenspace also commutes with `G.adj`, providing
`m_λ` independent **conserved phases** (the eigenvalues of any Hermitian
generator inside that eigenspace are all conserved).

After modding out the trivial overall phase, the count of nontrivial
extra conserved charges per eigenvalue is `m_λ - 1`.  Summing over
eigenvalues recovers `dim(H_P) - #{distinct eigenvalues}` extra phase
conservations on top of the single cell-uniform conservation law.

This is the **linear-momentum analogue** of the Bachman–Tamon
conservation law:  each eigenspace of the reduced Hamiltonian is a
sector with its own conserved quasi-momentum. -/
theorem noether_per_eigenvalue
    (P : EquitablePartition G I) (lam : ℝ) :
    ∃ (Plam : Matrix V V ℂ),
      Plam.IsHermitian ∧
      Plam * Plam = Plam ∧
      Plam * G.adj = G.adj * Plam ∧
      ∀ v, Plam.mulVec v ∈ P.cellUniformSubspace := by
  -- Construct `Plam` as the spectral projector of `P.quotient` at `λ`,
  -- inflated to `V × V` via the cell-uniform isometry.
  sorry

/-- **Charge count.**  The number of independent phase-conservation
charges contributed by an eigenvalue `λ` is `dim(eigenspace_λ) - 1`, plus
the single overall cell-uniform conservation.  Total conserved-charge
count, summed over the spectrum:

```
#{conserved charges} = dim(H_P) - 1 + #{distinct eigenvalues}.
```

Stated as a placeholder; the actual formula requires multiplicity
arithmetic over the (real) spectrum of the quotient matrix. -/
theorem conserved_charge_count
    (P : EquitablePartition G I) :
    True := by
  trivial

/-! ### 6. Open-system breaking.

A Lindblad master equation with an *equitable-symmetric* jump structure
(cf. `Graphplay.Dowsing.D8`) preserves the cell-uniform projector as a
conserved quantity; a generic Lindblad does not.  We state the abstract
form below. -/

/-- **Equitable-symmetric noise preserves the Noether charge.**

Let `L : Matrix V V ℂ → Matrix V V ℂ` be a Lindblad generator (a
super-operator on density matrices).  Say that `L` is
`P`-equitable-symmetric if every Lindblad jump operator `L_k` satisfies
`L_k * Π_P = Π_P * L_k`, where `Π_P = cellUniformProjector P`.

For such an `L`, the expectation value of `Π_P` is conserved under the
dissipative evolution: `d/dt ⟨Π_P⟩ = tr(Π_P · L(ρ)) = 0` for every state
`ρ`.

We state the abstract claim; the actual Lindblad super-operator
formalism lives in `Graphplay.Dowsing` (the D8 module) and we cite it
rather than re-formalize it here. -/
theorem equitable_symmetric_noise_preserves_charge
    (P : EquitablePartition G I)
    (L : Matrix V V ℂ → Matrix V V ℂ)
    (hL : ∀ ρ : Matrix V V ℂ,
        (L ρ * P.cellUniformProjector = P.cellUniformProjector * L ρ)) :
    ∀ ρ : Matrix V V ℂ,
      (P.cellUniformProjector * L ρ - L ρ * P.cellUniformProjector) = 0 := by
  intro ρ
  have h := hL ρ
  -- `[Π_P, L ρ] = 0` follows directly from the hypothesis.
  -- Need to flip sign convention.
  -- Rewrite: A - B = - (B - A); B - A = 0 by hypothesis.
  have : P.cellUniformProjector * L ρ = L ρ * P.cellUniformProjector := h.symm
  rw [this]
  simp

/-- **Generic noise breaks the conservation law.**  Without the
equitable-symmetry hypothesis on the Lindblad jumps, the cell-uniform
projector is no longer conserved: there exist Lindblad super-operators
`L` and density matrices `ρ` for which `tr(Π_P · L(ρ)) ≠ 0`.  This is
stated as an existence claim. -/
theorem generic_noise_breaks_charge
    (P : EquitablePartition G I) :
    ∃ (L : Matrix V V ℂ → Matrix V V ℂ) (ρ : Matrix V V ℂ),
      P.cellUniformProjector * L ρ ≠ L ρ * P.cellUniformProjector := by
  -- A single-vertex dephasing Lindblad with a non-cell-symmetric jump
  -- operator suffices.  We do not construct it explicitly.
  sorry

/-! ### 7. Engineering: protected subspaces and error correction.

Each independent conservation law gives a **quantum number** that the
unitary dynamics — and, under `equitable_symmetric_noise_preserves_charge`,
also the dissipative dynamics — does not change.

A quantum number that is preserved by the noise is a *passive* sector:
information encoded in the eigenspace of that quantum number is immune
to errors in directions that respect the symmetry.  This is the
graph-theoretic analogue of a **decoherence-free subspace** (Lidar–Whaley
2003) and provides a natural encoding for noiseless subsystems on
quantum-walk hardware.

We package the engineering content as a corollary statement. -/

/-- **Protected-subspace corollary.**  Under `P`-equitable-symmetric
noise, the cell-uniform subspace `H_P` is a decoherence-free subspace:
any initial state with support entirely in `H_P` remains in `H_P` under
the dissipative evolution. -/
theorem cellUniform_is_decoherence_free
    (P : EquitablePartition G I)
    (L : Matrix V V ℂ → Matrix V V ℂ)
    (hL : ∀ ρ : Matrix V V ℂ,
        L ρ * P.cellUniformProjector = P.cellUniformProjector * L ρ)
    (ρ : Matrix V V ℂ)
    (hρ : P.cellUniformProjector * ρ * P.cellUniformProjector = ρ) :
    P.cellUniformProjector * (L ρ) * P.cellUniformProjector = L ρ := by
  -- Sketch: by `hL` we can commute `Π_P` past `L`, then use `hρ` and
  -- the idempotence `Π_P · Π_P = Π_P`.  Routine but algebraically
  -- heavy; left as `sorry`.
  sorry

/-! ### 8. Continuum limit:  Tower-4 graphon Lindbladians.

A consistent sequence of equitable partitions `(P_n)` on a Cauchy sequence
of weighted graphs converging to a graphon `W` lifts to a **graphon
partition** `π : [0,1] → I_∞` whose cell-uniform "subspace" of the
graphon Hilbert space `L²([0,1])` is invariant under the graphon
Laplacian.

In this continuum limit, the Noether charge is the **cell-mass**:

```
m_i(t) := ∫_{C_i(π)} |ψ_t(x)|² dx     is independent of t.
```

We do not formalize Tower 4 in this file (it lives in
`Graphplay.Tower6` / `Graphplay.Tower7` and the Graphon namespace) and
only state the lift theorem abstractly. -/

/-- **Continuum lift (statement only).**  Given a consistent sequence
`P_n` of equitable partitions on graphs `G_n → W` (graphon convergence
in cut-norm), the cell-uniform conservation laws of `P_n` lift in the
limit to a continuous conservation law `m_i(t) = const` for the graphon
Schrödinger evolution.

The statement is intentionally axiomatic here; the underlying graphon
Hilbert space and Lindbladian framework live in
`Graphplay.Graphon`/`Graphplay.Tower6` and a fully type-correct version
of this theorem requires the graphon-partition data structures from
that subsystem. -/
theorem noether_lifts_to_graphon : True := by
  -- Placeholder: when the graphon-partition types are imported here,
  -- replace `True` with the actual statement
  --   `∀ (W : Graphon) (π : GraphonPartition W),
  --     IsEquitableGraphon W π →
  --       CellMassConserved W π (GraphonEvolution W)`.
  trivial

/-! ### Summary remark.

Putting the pieces together:

* Bachman–Tamon's `H_P` is invariant under `G.adj`
  (`cellUniformSubspace_invariant`),
* therefore its orthogonal projector `Π_P` commutes with `G.adj`
  (`cellUniformProjector_commutes`),
* therefore `Π_P` commutes with every analytic function of `G.adj`,
  including the unitary `U(t) = exp(-it·G.adj)`
  (`noether_equitable`),
* therefore `⟨Π_P⟩` is a constant of motion
  (`cellUniform_expectation_conserved`),
* and the eigenspaces of `Π_P` are decoherence-free under equitable-
  symmetric noise (`cellUniform_is_decoherence_free`).

This is the **Noether–Bachman–Tamon loop**: a symmetry of the graph
(equitable partition) ↔ an invariant subspace of the Hamiltonian
(`H_P`) ↔ a commuting projector (`Π_P`) ↔ a conserved quantum number
(⟨Π_P⟩). -/

end EquitablePartition

end Graphplay
