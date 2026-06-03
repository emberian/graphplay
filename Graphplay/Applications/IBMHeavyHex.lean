/-
# Graphplay.Applications.IBMHeavyHex

## Worked-example spectral disassembly of IBM's heavy-hexagonal lattice.

IBM's superconducting processor family — Eagle (127 qubits), Heron (133),
Osprey (433), Condor (1121) — share a fixed connectivity skeleton called the
**heavy-hexagonal lattice**: a (boundary-truncated) honeycomb lattice in which
every edge has been subdivided by a degree-2 "flag" qubit.  Data qubits sit at
honeycomb vertices and have degree at most 3; flag qubits sit on subdivided
edges and have degree exactly 2.  The resulting graph is bipartite and planar.

> **HONEST SCOPE — READ FIRST.**  Despite the IBM-hardware framing, *what this
> file actually builds and proves theorems about is **not** the honeycomb
> heavy-hex chip.*  The graph `HeavyHexLattice n m` realized and analyzed below
> is the **edge-subdivision of the complete graph `K_N`** on the `N = 2nm`
> sites (a flag qubit on **every** ordered distinct pair of sites), so each data
> site has degree `2(N−1)` and the symmetric quotient coupling is `2√(N−1)` —
> **not** the honeycomb interior degree `3` / coupling `√6` advertised in the
> physics paragraph above.  Concretely this is *a generic `K_N`-site-subdivision
> equitable result wearing hardware names*: the data/flag equitable partition,
> the exact `2×2` quotient, the PST/mixing/spectrum theorems are all faithful to
> the `K_N`-subdivision they are stated on, and they are honestly worth having
> as a worked equitable-disassembly example — but the **honeycomb degree-3
> topology is not built**.  The genuine honeycomb template `HoneycombAdj` /
> `HoneycombLattice` *is* defined (and is the truncated honeycomb), but it is
> used **only** as the base of `heavyHexAsBundle` (with trivial `Unit` fibers,
> so it carries no flag qubits and does not reconstruct the chip); it is **never
> used as the chip adjacency**.  Matching the real honeycomb degrees / the real
> physical qubit counts would require the boundary-truncated subdivision and a
> hardware-truncation vertex subset, neither of which is developed here.  Every
> docstring below that mentions `3`, `√6`, or "honeycomb interior degree" as the
> realized value is describing the *template* it is **not** building; the
> realized values are the `K_N` ones `2(N−1)` / `2√(N−1)`.

References (public):

* C. Chamberland, G. Zhu, T. Yoder, J. Hertzberg, A. Cross,
  "Topological and subsystem codes on low-degree graphs with flag qubits"
  (Phys. Rev. X 10, 011022; arXiv:1907.09528 / 2003.07770).
* J. Gambetta, "IBM Quantum roadmap and Eagle / Heron / Condor processors"
  (IBM Research Blog, 2021–2024).
* IBM Quantum hardware documentation:
  <https://docs.quantum.ibm.com/guides/processor-types>.

The combinatorial content extracted in this file is that the realized graph is
an **edge-subdivision** with a data/flag bipartition (the `K_N`-site
subdivision, per the scope note above — not the honeycomb subdivision).  This
presentation buys us, for free, a 2-cell equitable partition (data / flag), an
exact 2x2 quotient matrix, a (data-only, `Unit`-fiber) graph-bundle handle over
the honeycomb template, and all of the lifting theorems from `Graphplay.PST`,
`Graphplay.Mixing`, `Graphplay.Search`, and `Graphplay.Chiral`.

## Layout of the file

1. `HoneycombLattice n m` — a finite honeycomb-lattice `SimpleGraph` on
   an `n × m` brick-wall coordinate grid.
2. `HeavyHexLattice n m` — the realized chip graph: the **complete-site**
   edge-subdivision (a flag on every ordered distinct pair of sites), data/flag
   tagged.  (This is `K_N`-subdivision, not honeycomb-subdivision; see scope.)
3. **Spectral disassembly**:
   - `dataFlagPartition` — the role partition into data vs. flag qubits.
   - `dataFlagQuotient` — the 2x2 quotient matrix.
   - `heavyHexAsBundle` — a `GraphBundle` over the honeycomb template with
     **trivial `Unit` fibers** (so it models only the *data* sublattice, not the
     flag qubits — see its docstring; it is NOT a faithful chip model).
4. **Lifting** — PST / mixing / search / chiral statements on the quotient
   lifting to cell-uniform statements on the chip.
5. **Hardware spec** — a concrete `HardwareSpec` matching IBM Heron / Eagle.
6. **Three concrete engineering payoffs** — PST between two named data
   qubits, noise-symmetric subspaces, chiral-signing fast mixing.

The combinatorial / spectral-disassembly core is now *proved* (equitable
partition, exact `2×2` quotient `[[0, 2(N−1)],[2, 0]]`, symmetric quotient
`[[0, 2√(N−1)],[2√(N−1), 0]]`, cell cardinalities, dart counts, the **explicit
`2×2` matrix exponential** `exp(c·M) = Ur·diag(e^{cq},e^{−cq})·Ur⁻¹` with closed
off-diagonal `sinh`/`sin`, the **exact spectrum** `{±2√(N−1)}` of the raw quotient
via `det(λI−Q) = λ²−4(N−1)`, the **PST** at `τ = π/(2q)` and uniform mixing at
`π/(4q)`, the PST lift via `pst_lift`, the three engineering payoffs (PST,
noise-symmetric subspaces with a genuine asymmetry witness, and the chiral
*no-speedup* negative result — now in its strong **phase-independent spectrum**
form `dataFlag_chiral_spectrum_phase_independent`).  The remaining `sorry`s are
the genuinely chip-parameter / upstream-machinery leaves: the bundle re-indexing
bijection, the `Mixing`/`Search` lifts (blocked on upstream `sorry`s), the
automorphism-averaged two-qubit PST, the explicit `HardwareSpec` satisfaction,
and the 3-cell refined chiral speedup — each carrying a one-line honest reason at
its site.
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Sum.Basic
import Graphplay.Weighted
import Graphplay.Equitable
import Graphplay.Bundle
import Graphplay.Chiral
import Graphplay.PST
import Graphplay.Mixing
import Graphplay.Search
import Graphplay.Toolkit.Hardware
import Graphplay.Toolkit.Noise

open scoped Matrix

universe u v

namespace Graphplay
namespace Applications
namespace IBMHeavyHex

/-! ## 1. The honeycomb template.

We model the honeycomb (hex) lattice as a `SimpleGraph` on the brick-wall
coordinate space `Fin n × Fin m × Bool`, where the `Bool` distinguishes the
two sublattices A and B of the bipartite honeycomb.  Adjacency follows the
usual three offsets `(0, 0)`, `(0, +1)`, `(+1, 0)` between the A and B
sublattices, with the convention that adjacency is *only* between an A-vertex
and a B-vertex.  We do not impose periodic boundaries: the lattice is finite,
with reduced degree on the boundary, matching real IBM chips. -/

/-- Vertex type of the honeycomb template: rows `Fin n`, columns `Fin m`,
sublattice tag `Bool` (`false` = A, `true` = B). -/
abbrev HoneyVertex (n m : ℕ) : Type := Fin n × Fin m × Bool

/-- Adjacency relation for the honeycomb lattice on an `n × m` brick-wall
coordinate grid.  Adjacency runs only between the A-sublattice (`Bool = false`)
and the B-sublattice (`Bool = true`); the three brick-wall offsets `(0,0)`,
`(0,+1)`, `(+1,0)` (taken on the integer coordinates, *without* wrap-around)
realize the hexagonal lattice with reduced degree on the boundary — exactly the
boundary-truncated shape of a physical IBM chip.  We symmetrize the oriented
A→B pattern explicitly so that `symm`/`loopless` are immediate. -/
def HoneycombAdj (n m : ℕ) : HoneyVertex n m → HoneyVertex n m → Prop :=
  fun x y =>
    -- A→B edges (x is A at (i,j), y is B at (i',j')):
    (x.2.2 = false ∧ y.2.2 = true ∧
      (((y.1.val = x.1.val) ∧ (y.2.1.val = x.2.1.val)) ∨
       ((y.1.val = x.1.val) ∧ (y.2.1.val = x.2.1.val + 1)) ∨
       ((y.1.val = x.1.val + 1) ∧ (y.2.1.val = x.2.1.val)))) ∨
    -- B→A edges (x is B, y is A): the mirror, swapping roles.
    (x.2.2 = true ∧ y.2.2 = false ∧
      (((x.1.val = y.1.val) ∧ (x.2.1.val = y.2.1.val)) ∨
       ((x.1.val = y.1.val) ∧ (x.2.1.val = y.2.1.val + 1)) ∨
       ((x.1.val = y.1.val + 1) ∧ (x.2.1.val = y.2.1.val))))

instance (n m : ℕ) : DecidableRel (HoneycombAdj n m) := by
  intro x y; unfold HoneycombAdj; infer_instance

/-- The honeycomb lattice as a Mathlib `SimpleGraph` on the brick-wall grid.
Symmetry holds because the A→B and B→A disjuncts are mirror images of each
other; looplessness holds because every edge crosses between the two
sublattices (`false ≠ true`), so no vertex is adjacent to itself. -/
def HoneycombLattice (n m : ℕ) : SimpleGraph (HoneyVertex n m) where
  Adj := HoneycombAdj n m
  symm := by
    intro x y h
    unfold HoneycombAdj at h ⊢
    rcases h with ⟨hxA, hyB, hpat⟩ | ⟨hxB, hyA, hpat⟩
    · -- x is A, y is B  ⇒  swap into the B→A disjunct.
      exact Or.inr ⟨hyB, hxA, hpat⟩
    · -- x is B, y is A  ⇒  swap into the A→B disjunct.
      exact Or.inl ⟨hyA, hxB, hpat⟩
  loopless := ⟨by
    rintro x (⟨hA, hB, _⟩ | ⟨hA, hB, _⟩) <;>
      · rw [hA] at hB; exact absurd hB (by decide)⟩

/-- The honeycomb is `3`-regular in the interior (degree drops on the truncated
boundary).  We record the interior degree as a named constant. -/
def honeycombInteriorDegree : ℕ := 3

/-! ## 2. The heavy-hex lattice as edge-subdivision.

Edge-subdivision of a graph `Q` inserts one new vertex into every edge.
Concretely, a vertex of the subdivision is either:
* a `Data v`, where `v : HoneyVertex`, or
* a `Flag e`, where `e` is an edge of the honeycomb.

For our finite-finite-finite construction we encode edges of the honeycomb
as ordered pairs `(u, v)` with `u < v` (in some chosen linear order) and
`Q.Adj u v`.  To avoid spelling out the edge subset on a finite linear order,
we coarsely take the vertex type as `Data ⊕ (HoneyVertex × HoneyVertex)` and
restrict via the adjacency predicate in the adjacency relation itself. -/

/-- An (ordered) **honeycomb dart**: a pair of *distinct* honeycomb sites.
Each undirected pair `{a, b}` with `a ≠ b` is realized by the two darts
`(a, b)` and `(b, a)`; a *flag* qubit will be placed on each dart.  Using a
`Subtype` (rather than all of `HoneyVertex × HoneyVertex`) removes the diagonal
`(a, a)` "phantom" pairs, which is exactly what makes the data/flag partition
genuinely *equitable* (every flag then has exactly two data-neighbours). -/
abbrev HoneyDart (n m : ℕ) : Type :=
  { p : HoneyVertex n m × HoneyVertex n m // p.1 ≠ p.2 }

/-- Vertex type of the heavy-hex lattice: data qubits + flag qubits.  Data
qubits sit at honeycomb sites; flag qubits sit on honeycomb darts (ordered
distinct pairs).  Modelling flags over darts rather than all pairs is the
faithful "edge-subdivision of the complete template on distinct sites": every
flag qubit is incident to exactly its two endpoint data qubits. -/
inductive HeavyHexVertex (n m : ℕ) : Type
  | data (v : HoneyVertex n m) : HeavyHexVertex n m
  | flag (e : HoneyDart n m) : HeavyHexVertex n m
deriving DecidableEq

namespace HeavyHexVertex

/-- The canonical encoding of a heavy-hex vertex as a sum
`HoneyVertex ⊕ HoneyDart`. -/
def toSum {n m : ℕ} :
    HeavyHexVertex n m → HoneyVertex n m ⊕ HoneyDart n m
  | .data v => Sum.inl v
  | .flag e => Sum.inr e

/-- Inverse to `toSum`: rebuild a `HeavyHexVertex` from the sum encoding. -/
def ofSum {n m : ℕ} :
    HoneyVertex n m ⊕ HoneyDart n m → HeavyHexVertex n m
  | Sum.inl v => .data v
  | Sum.inr e => .flag e

@[simp] theorem ofSum_toSum {n m : ℕ} (x : HeavyHexVertex n m) :
    ofSum (toSum x) = x := by
  cases x <;> rfl

@[simp] theorem toSum_ofSum {n m : ℕ}
    (x : HoneyVertex n m ⊕ HoneyDart n m) :
    toSum (ofSum x) = x := by
  rcases x with v | e <;> rfl

/-- `HeavyHexVertex n m ≃ HoneyVertex n m ⊕ HoneyDart n m`. -/
def equivSum {n m : ℕ} :
    HeavyHexVertex n m ≃ HoneyVertex n m ⊕ HoneyDart n m where
  toFun := toSum
  invFun := ofSum
  left_inv := ofSum_toSum
  right_inv := toSum_ofSum

end HeavyHexVertex

instance (n m : ℕ) : Fintype (HoneyDart n m) := by
  unfold HoneyDart; infer_instance

instance (n m : ℕ) : Fintype (HeavyHexVertex n m) :=
  Fintype.ofEquiv _ HeavyHexVertex.equivSum.symm

/-- The number of honeycomb darts incident to a fixed site `v₀` is `2·(N−1)`,
where `N = |HoneyVertex n m|`.  Each incident dart is either `(v₀, w)` or
`(w, v₀)` for a *distinct* second site `w ≠ v₀`; the two families are disjoint
(a dart has distinct endpoints), giving the factor `2`. -/
theorem card_darts_incident (n m : ℕ) (v₀ : HoneyVertex n m) :
    (Finset.univ.filter
        (fun e : HoneyDart n m => v₀ = e.val.1 ∨ v₀ = e.val.2)).card
      = 2 * (Fintype.card (HoneyVertex n m) - 1) := by
  classical
  -- Bijection `Bool × {w // w ≠ v₀} ≃ {incident darts}`:
  -- `(false, w) ↦ (v₀, w)`, `(true, w) ↦ (w, v₀)`.
  have hcard : (Finset.univ.filter
        (fun e : HoneyDart n m => v₀ = e.val.1 ∨ v₀ = e.val.2)).card
      = Fintype.card (Bool × {w : HoneyVertex n m // w ≠ v₀}) := by
    rw [← Fintype.card_coe]
    apply Fintype.card_congr
    refine ⟨fun e => (decide (v₀ = e.val.val.1),
        if h : v₀ = e.val.val.1
          then (⟨e.val.val.2, fun hc => e.val.property (h.symm.trans hc.symm)⟩ :
                  {w : HoneyVertex n m // w ≠ v₀})
          else ⟨e.val.val.1, fun hc => h hc.symm⟩),
      fun p => ⟨⟨if p.1 then (v₀, p.2.val) else (p.2.val, v₀), ?_⟩, ?_⟩,
      ?_, ?_⟩
    · cases hb : p.1 <;> simp [hb, p.2.property, Ne.symm p.2.property]
    · -- membership in the filter
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      cases hb : p.1 <;> simp [hb]
    · -- left inverse
      rintro ⟨⟨⟨a, b⟩, hd⟩, hmem⟩
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      simp only [ne_eq] at hd
      by_cases hc : v₀ = a
      · simp only [hc, decide_true, if_true, ↓reduceDIte, Subtype.mk.injEq]
      · simp only [hc, decide_false, if_neg hc, ↓reduceDIte, Subtype.mk.injEq]
        rcases hmem with h1 | h2
        · exact absurd h1 hc
        · subst h2; simp
    · -- right inverse
      rintro ⟨b, ⟨w, hw⟩⟩
      cases b <;>
        simp [Ne.symm hw, hw, Subtype.ext_iff]
  rw [hcard, Fintype.card_prod, Fintype.card_bool,
    Fintype.card_subtype_compl, Fintype.card_subtype_eq]

/-- Adjacency of heavy-hex: a `data u` is adjacent to a `flag e` exactly when
`u` is one of the two endpoints `e.1.1` or `e.1.2` of the dart `e`.  Flag-flag
and data-data adjacencies are forbidden.  Because every dart has two *distinct*
endpoints, every flag is adjacent to exactly two data qubits. -/
def HeavyHexAdj (n m : ℕ) :
    HeavyHexVertex n m → HeavyHexVertex n m → Prop
  | .data u, .flag e => u = e.val.1 ∨ u = e.val.2
  | .flag e, .data u => u = e.val.1 ∨ u = e.val.2
  | _, _ => False

instance (n m : ℕ) : DecidableRel (HeavyHexAdj n m) := by
  intro x y
  cases x <;> cases y <;> (unfold HeavyHexAdj; infer_instance)

/-- The heavy-hexagonal lattice on an `n × m` site base, as a Mathlib
`SimpleGraph`.  Vertices are tagged data / flag; edges only go between data and
flag.  Symmetry is by the symmetric shape of `HeavyHexAdj`; looplessness holds
because data-data and flag-flag adjacencies are `False`. -/
def HeavyHexLattice (n m : ℕ) : SimpleGraph (HeavyHexVertex n m) where
  Adj := HeavyHexAdj n m
  symm := by
    intro x y h
    cases x <;> cases y <;> simp_all [HeavyHexAdj]
  loopless := ⟨by
    rintro x h
    cases x <;> simp_all [HeavyHexAdj]⟩

/-- The 0/1 Hermitian weighted graph attached to `HeavyHexLattice n m`. -/
noncomputable def heavyHexWeighted (n m : ℕ) :
    WeightedGraph (HeavyHexVertex n m) := by
  classical
  exact Graphplay.SimpleGraph.toWeighted (HeavyHexLattice n m)

/-! ### Named processor sizes.

We expose three IBM-shaped instances by selecting `(n, m)` pairs that match
the reported physical qubit counts.  The exact `n × m` shape of each IBM
processor is given in IBM's hardware documentation; we approximate it here
with rectangles whose vertex count matches.  Heron has 133 qubits arranged
in a heavy-hex lattice with row offset; the closest brick-wall rectangle is
`(7, 19)` (giving 133 data qubits before flags).  Eagle has 127, matching
`(7, 18)` with one truncated row. -/

/-- The heavy-hex lattice underlying IBM Eagle (127 qubits, 2022). -/
noncomputable def heavyHexEagle : WeightedGraph (HeavyHexVertex 7 18) :=
  heavyHexWeighted 7 18

/-- The heavy-hex lattice underlying IBM Heron (133 qubits, 2023). -/
noncomputable def heavyHexHeron : WeightedGraph (HeavyHexVertex 7 19) :=
  heavyHexWeighted 7 19

/-- The heavy-hex lattice underlying IBM Condor (1121 qubits, 2023). -/
noncomputable def heavyHexCondor : WeightedGraph (HeavyHexVertex 33 34) :=
  heavyHexWeighted 33 34

/-! ## 3. Spectral disassembly.

We find a natural equitable partition by *vertex role* — data vs. flag —
and read off the 2x2 quotient matrix. -/

/-- The two roles a heavy-hex vertex can play. -/
inductive Role : Type
  | data : Role
  | flag : Role
deriving DecidableEq, Fintype, Repr

/-- The role of a heavy-hex vertex: data if it came from a honeycomb vertex,
flag if it was inserted on a dart. -/
def role {n m : ℕ} : HeavyHexVertex n m → Role
  | .data _ => Role.data
  | .flag _ => Role.flag

/-- A site permutation `π` of `HoneyVertex` lifts to a permutation of
`HeavyHexVertex`: relabel `data u` by `π u` and relabel each dart endpointwise.
This lift is a graph automorphism of `HeavyHexLattice` preserving roles, and is
the engine of equitability — any two same-role vertices are related by such a
lift, so they have identical branching numbers. -/
def liftPerm {n m : ℕ} (π : Equiv.Perm (HoneyVertex n m)) :
    Equiv.Perm (HeavyHexVertex n m) where
  toFun
    | .data u => .data (π u)
    | .flag e => .flag ⟨(π e.val.1, π e.val.2), by
        simp only [ne_eq, π.injective.eq_iff]; exact e.property⟩
  invFun
    | .data u => .data (π.symm u)
    | .flag e => .flag ⟨(π.symm e.val.1, π.symm e.val.2), by
        simp only [ne_eq, π.symm.injective.eq_iff]; exact e.property⟩
  left_inv := by rintro (u | ⟨⟨a, b⟩, h⟩) <;> simp
  right_inv := by rintro (u | ⟨⟨a, b⟩, h⟩) <;> simp

/-- The lift preserves roles. -/
theorem role_liftPerm {n m : ℕ} (π : Equiv.Perm (HoneyVertex n m))
    (x : HeavyHexVertex n m) : role (liftPerm π x) = role x := by
  cases x <;> rfl

/-- The lift preserves heavy-hex adjacency. -/
theorem heavyHexAdj_liftPerm {n m : ℕ} (π : Equiv.Perm (HoneyVertex n m))
    (x y : HeavyHexVertex n m) :
    HeavyHexAdj n m (liftPerm π x) (liftPerm π y) ↔ HeavyHexAdj n m x y := by
  cases x <;> cases y <;>
    simp only [liftPerm, HeavyHexAdj, Equiv.coe_fn_mk, π.injective.eq_iff]

/-- The data/flag branching number depends only on the *role* of the source
vertex: it is invariant under any site-permutation lift.  This is the heart of
equitability. -/
theorem branching_liftPerm {n m : ℕ} (π : Equiv.Perm (HoneyVertex n m))
    (j : Role) (x : HeavyHexVertex n m) :
    (∑ z, (if role z = j then (heavyHexWeighted n m).adj (liftPerm π x) z else 0))
      = ∑ z, (if role z = j then (heavyHexWeighted n m).adj x z else 0) := by
  classical
  -- Reindex the sum by `z = liftPerm π z'`.
  rw [← Equiv.sum_comp (liftPerm π) (fun z =>
        if role z = j then (heavyHexWeighted n m).adj (liftPerm π x) z else 0)]
  apply Finset.sum_congr rfl
  intro z' _
  rw [role_liftPerm]
  by_cases hrole : role z' = j
  · simp only [hrole, if_true]
    -- `adj (Φ x) (Φ z') = adj x z'` by automorphism.
    show (heavyHexWeighted n m).adj (liftPerm π x) (liftPerm π z')
       = (heavyHexWeighted n m).adj x z'
    unfold heavyHexWeighted Graphplay.SimpleGraph.toWeighted
    simp only [SimpleGraph.adjMatrix_apply]
    show (if HeavyHexLattice n m |>.Adj (liftPerm π x) (liftPerm π z') then (1:ℂ) else 0)
       = (if HeavyHexLattice n m |>.Adj x z' then (1:ℂ) else 0)
    rw [show (HeavyHexLattice n m).Adj = HeavyHexAdj n m from rfl,
        heavyHexAdj_liftPerm]
  · simp only [hrole, if_false]

/-- The **data/flag role partition** of the heavy-hex lattice.

This is the central equitable partition extracted in this file.

* Every flag vertex has exactly degree `2`: it sits on a dart `(a, b)` with
  `a ≠ b`, so it is adjacent to exactly the two data qubits `data a`, `data b`.
* Every data vertex `data u` is adjacent to exactly the `2·(N-1)` flag qubits
  whose dart has `u` as an endpoint (`N = |HoneyVertex|`).

Both counts are independent of the chosen representative, because any two
same-role vertices are related by a site-permutation lift (`liftPerm`), under
which the heavy-hex adjacency and the role labelling are invariant
(`heavyHexAdj_liftPerm`, `role_liftPerm`).  Hence the partition is equitable,
with `2×2` quotient

      Q  =  ⎡ 0       2(N-1) ⎤
            ⎣ 2       0      ⎦.

(On the honeycomb *template* itself — as opposed to the complete site graph
realized here — the data row sum would be the honeycomb degree `3` in the
interior; that boundary-truncated variant needs the 3-cell `Role` refinement
`{data-deg-3, data-deg-2, flag}`.) -/
def dataFlagPartition (n m : ℕ) :
    EquitablePartition (heavyHexWeighted n m) Role where
  cells := role
  uniform := by
    -- Two same-role vertices `x, y` are related by a site-permutation lift:
    -- `data u, data u'` by `Equiv.swap u u'`; `flag e, flag e'` by any perm
    -- carrying the dart `e` to `e'`.  `branching_liftPerm` then equates them.
    intro i j x y hx hy
    -- Build a site permutation `π` with `liftPerm π x = y`.
    obtain ⟨π, hπ⟩ : ∃ π : Equiv.Perm (HoneyVertex n m), liftPerm π x = y := by
      cases x with
      | data u =>
        cases y with
        | data u' => exact ⟨Equiv.swap u u', by simp [liftPerm]⟩
        | flag e' => exact absurd (hx.trans hy.symm) (by simp [role])
      | flag e =>
        cases y with
        | data u' => exact absurd (hx.trans hy.symm) (by simp [role])
        | flag e' =>
          -- A permutation sending `e.1 ↦ e'.1` and `e.2 ↦ e'.2`.
          obtain ⟨⟨a, b⟩, hab⟩ := e
          obtain ⟨⟨a', b'⟩, hab'⟩ := e'
          simp only [ne_eq] at hab hab'
          -- `π₁ = swap a a'` maps `a ↦ a'`.  Then `π₁ b ≠ a'` (since `b ≠ a`),
          -- so `π₂ = swap (π₁ b) b'` fixes `a'` and maps `π₁ b ↦ b'`.
          set π₁ : Equiv.Perm (HoneyVertex n m) := Equiv.swap a a' with hπ₁
          have hπ₁b : π₁ b ≠ a' := by
            rw [hπ₁]
            intro hcontra
            -- swap a a' b = a' forces b = a, contradiction.
            have : b = a := by
              by_contra hba
              rcases eq_or_ne b a' with hba' | hba'
              · -- b = a' and swap a a' a' = a  ⇒  a = a', so b = a' = a, contradiction.
                rw [hba', Equiv.swap_apply_right] at hcontra
                exact hba (hba'.trans hcontra.symm)
              · rw [Equiv.swap_apply_of_ne_of_ne hba hba'] at hcontra
                exact hba' hcontra
            exact hab this.symm
          refine ⟨(Equiv.swap (π₁ b) b') * π₁, ?_⟩
          -- Verify the lift carries `flag (a,b) ↦ flag (a',b')`.
          simp only [liftPerm, Equiv.Perm.mul_apply, Equiv.coe_fn_mk,
            HeavyHexVertex.flag.injEq, Subtype.mk.injEq, Prod.mk.injEq]
          refine ⟨?_, ?_⟩
          · -- first endpoint: π₂ (π₁ a) = π₂ a' = a' (a' fixed by π₂).
            have : π₁ a = a' := by rw [hπ₁]; exact Equiv.swap_apply_left a a'
            rw [this, Equiv.swap_apply_of_ne_of_ne (Ne.symm hπ₁b) hab']
          · -- second endpoint: π₂ (π₁ b) = b'.
            rw [Equiv.swap_apply_left]
    rw [← hπ, branching_liftPerm]

/-- The 2 x 2 quotient matrix of the data/flag role partition of the realized
`K_N`-site-subdivision graph.  Its proven entries (see
`dataFlagQuotient_toroidal_form`) are: `(data, flag) = 2(N−1)` (the dart count
at a data site, `N = |HoneyVertex| = 2nm`), `(flag, data) = 2`, diagonal `0`.

(NB: this is the `K_N` value `2(N−1)`, **not** the honeycomb interior degree `3`
— see the file-header scope note; the boundary-truncated honeycomb template is
not the graph realized here.)  Concrete numerical content lifted into `ℂ`. -/
noncomputable def dataFlagQuotient (n m : ℕ) : Matrix Role Role ℂ :=
  (dataFlagPartition n m).quotient

/-- Branching of a `data u` vertex: into the flag cell it is the number of darts
incident to `u`, namely `2·(N−1)`; into the data cell it is `0`
(data-data edges do not exist). -/
theorem branching_data (n m : ℕ) (u : HoneyVertex n m) :
    (dataFlagPartition n m).branching Role.flag (HeavyHexVertex.data u)
        = (2 * (Fintype.card (HoneyVertex n m) - 1) : ℕ)
      ∧ (dataFlagPartition n m).branching Role.data (HeavyHexVertex.data u) = 0 := by
  classical
  constructor
  · -- branching into the flag cell
    unfold EquitablePartition.branching
    show (∑ z, if (dataFlagPartition n m).cells z = Role.flag then
            (heavyHexWeighted n m).adj (HeavyHexVertex.data u) z else 0)
        = (2 * (Fintype.card (HoneyVertex n m) - 1) : ℕ)
    -- Reindex over `HoneyVertex ⊕ HoneyDart`: only `flag e` summands survive.
    rw [← Equiv.sum_comp HeavyHexVertex.equivSum.symm
          (fun z => if (dataFlagPartition n m).cells z = Role.flag then
            (heavyHexWeighted n m).adj (HeavyHexVertex.data u) z else 0),
        Fintype.sum_sum_type]
    have hleft : (∑ v : HoneyVertex n m,
        if (dataFlagPartition n m).cells (HeavyHexVertex.equivSum.symm (Sum.inl v))
            = Role.flag then
          (heavyHexWeighted n m).adj (HeavyHexVertex.data u)
            (HeavyHexVertex.equivSum.symm (Sum.inl v)) else 0) = 0 := by
      apply Finset.sum_eq_zero; intro v _
      rw [if_neg]; simp [HeavyHexVertex.equivSum, HeavyHexVertex.ofSum,
        dataFlagPartition, role]
    rw [hleft, zero_add]
    -- The flag summands: `adj (data u) (flag e) = 1` iff `u = e.1 ∨ u = e.2`.
    have hright : ∀ e : HoneyDart n m,
        (if (dataFlagPartition n m).cells (HeavyHexVertex.equivSum.symm (Sum.inr e))
            = Role.flag then
          (heavyHexWeighted n m).adj (HeavyHexVertex.data u)
            (HeavyHexVertex.equivSum.symm (Sum.inr e)) else 0)
        = (if u = e.val.1 ∨ u = e.val.2 then (1 : ℂ) else 0) := by
      intro e
      rw [if_pos (by simp [HeavyHexVertex.equivSum, HeavyHexVertex.ofSum,
        dataFlagPartition, role])]
      show (heavyHexWeighted n m).adj (HeavyHexVertex.data u) (HeavyHexVertex.flag e) = _
      unfold heavyHexWeighted Graphplay.SimpleGraph.toWeighted
      simp only [SimpleGraph.adjMatrix_apply]
      show (if (HeavyHexLattice n m).Adj (HeavyHexVertex.data u) (HeavyHexVertex.flag e)
              then (1:ℂ) else 0) = _
      rw [show (HeavyHexLattice n m).Adj = HeavyHexAdj n m from rfl,
        show HeavyHexAdj n m (HeavyHexVertex.data u) (HeavyHexVertex.flag e)
          = (u = e.val.1 ∨ u = e.val.2) from rfl]
      congr 1
    rw [Finset.sum_congr rfl (fun e _ => hright e), Finset.sum_boole,
      card_darts_incident]
  · -- branching into the data cell is 0
    unfold EquitablePartition.branching
    apply Finset.sum_eq_zero; intro z _
    rcases z with v | e
    · by_cases h : (dataFlagPartition n m).cells (HeavyHexVertex.data v) = Role.data
      · rw [if_pos h]
        show (heavyHexWeighted n m).adj (HeavyHexVertex.data u) (HeavyHexVertex.data v) = 0
        unfold heavyHexWeighted Graphplay.SimpleGraph.toWeighted
        simp only [SimpleGraph.adjMatrix_apply]
        rw [if_neg]; rw [show (HeavyHexLattice n m).Adj = HeavyHexAdj n m from rfl]; exact id
      · rw [if_neg h]
    · rw [if_neg]; simp [dataFlagPartition, role]

/-- Branching of a `flag e` vertex: into the data cell it is `2` (the two distinct
endpoints of the dart); into the flag cell it is `0`. -/
theorem branching_flag (n m : ℕ) (e : HoneyDart n m) :
    (dataFlagPartition n m).branching Role.data (HeavyHexVertex.flag e) = 2
      ∧ (dataFlagPartition n m).branching Role.flag (HeavyHexVertex.flag e) = 0 := by
  classical
  constructor
  · -- branching into the data cell: exactly the two endpoints
    unfold EquitablePartition.branching
    show (∑ z, if (dataFlagPartition n m).cells z = Role.data then
            (heavyHexWeighted n m).adj (HeavyHexVertex.flag e) z else 0) = 2
    rw [← Equiv.sum_comp HeavyHexVertex.equivSum.symm
          (fun z => if (dataFlagPartition n m).cells z = Role.data then
            (heavyHexWeighted n m).adj (HeavyHexVertex.flag e) z else 0),
        Fintype.sum_sum_type]
    have hright : (∑ d : HoneyDart n m,
        if (dataFlagPartition n m).cells (HeavyHexVertex.equivSum.symm (Sum.inr d))
            = Role.data then
          (heavyHexWeighted n m).adj (HeavyHexVertex.flag e)
            (HeavyHexVertex.equivSum.symm (Sum.inr d)) else 0) = 0 := by
      apply Finset.sum_eq_zero; intro d _
      rw [if_neg]; simp [HeavyHexVertex.equivSum, HeavyHexVertex.ofSum,
        dataFlagPartition, role]
    rw [hright, add_zero]
    have hleft : ∀ v : HoneyVertex n m,
        (if (dataFlagPartition n m).cells (HeavyHexVertex.equivSum.symm (Sum.inl v))
            = Role.data then
          (heavyHexWeighted n m).adj (HeavyHexVertex.flag e)
            (HeavyHexVertex.equivSum.symm (Sum.inl v)) else 0)
        = (if v = e.val.1 ∨ v = e.val.2 then (1 : ℂ) else 0) := by
      intro v
      rw [if_pos (by simp [HeavyHexVertex.equivSum, HeavyHexVertex.ofSum,
        dataFlagPartition, role])]
      show (heavyHexWeighted n m).adj (HeavyHexVertex.flag e) (HeavyHexVertex.data v) = _
      unfold heavyHexWeighted Graphplay.SimpleGraph.toWeighted
      simp only [SimpleGraph.adjMatrix_apply]
      show (if (HeavyHexLattice n m).Adj (HeavyHexVertex.flag e) (HeavyHexVertex.data v)
              then (1:ℂ) else 0) = _
      rw [show (HeavyHexLattice n m).Adj = HeavyHexAdj n m from rfl,
        show HeavyHexAdj n m (HeavyHexVertex.flag e) (HeavyHexVertex.data v)
          = (v = e.val.1 ∨ v = e.val.2) from rfl]
      congr 1
    rw [Finset.sum_congr rfl (fun v _ => hleft v), Finset.sum_boole]
    -- exactly two honey vertices satisfy `v = e.1 ∨ v = e.2` (distinct endpoints)
    have : (Finset.univ.filter (fun v : HoneyVertex n m => v = e.val.1 ∨ v = e.val.2)).card = 2 := by
      rw [show (Finset.univ.filter (fun v : HoneyVertex n m => v = e.val.1 ∨ v = e.val.2))
            = {e.val.1, e.val.2} by ext v; simp]
      exact (Finset.card_pair_eq_two_iff).mpr e.property
    rw [this]; norm_num
  · -- branching into the flag cell is 0 (no flag-flag edges)
    unfold EquitablePartition.branching
    apply Finset.sum_eq_zero; intro z _
    rcases z with v | d
    · rw [if_neg]; simp [dataFlagPartition, role]
    · by_cases h : (dataFlagPartition n m).cells (HeavyHexVertex.flag d) = Role.flag
      · rw [if_pos h]
        show (heavyHexWeighted n m).adj (HeavyHexVertex.flag e) (HeavyHexVertex.flag d) = 0
        unfold heavyHexWeighted Graphplay.SimpleGraph.toWeighted
        simp only [SimpleGraph.adjMatrix_apply]
        rw [if_neg]; rw [show (HeavyHexLattice n m).Adj = HeavyHexAdj n m from rfl]; exact id
      · rw [if_neg h]

/-- The data/flag quotient matrix in concrete form.  The `(data, flag)` entry is
the number of darts incident to a data site, `2·(N−1)` with `N = |HoneyVertex| =
2nm` (the **complete-site-subdivision** value realized by this file's
`HeavyHexLattice` — *not* the honeycomb-template interior degree `3`; see the
file header note #53).  The `(flag, data)` entry is `2` (each flag's two distinct
endpoints) and the diagonal vanishes.  We require `0 < n, 0 < m` so that both
cells are nonempty (otherwise an empty cell forces a `0` quotient row by the
`quotient` convention). -/
theorem dataFlagQuotient_toroidal_form (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    dataFlagQuotient n m Role.data Role.flag
        = (2 * (Fintype.card (HoneyVertex n m) - 1) : ℕ) ∧
    dataFlagQuotient n m Role.flag Role.data = 2 ∧
    dataFlagQuotient n m Role.data Role.data = 0 ∧
    dataFlagQuotient n m Role.flag Role.flag = 0 := by
  classical
  -- Representatives of each cell.
  let u₀ : HoneyVertex n m := (⟨0, hn⟩, ⟨0, hm⟩, false)
  have he₀ : ((⟨0, hn⟩, ⟨0, hm⟩, false) : HoneyVertex n m)
      ≠ (⟨0, hn⟩, ⟨0, hm⟩, true) := by simp
  let e₀ : HoneyDart n m :=
    ⟨((⟨0, hn⟩, ⟨0, hm⟩, false), (⟨0, hn⟩, ⟨0, hm⟩, true)), he₀⟩
  have hdataCell : (dataFlagPartition n m).cells (HeavyHexVertex.data u₀) = Role.data := rfl
  have hflagCell : (dataFlagPartition n m).cells (HeavyHexVertex.flag e₀) = Role.flag := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [dataFlagQuotient, (dataFlagPartition n m).quotient_apply Role.data Role.flag
        (HeavyHexVertex.data u₀) hdataCell]
    exact (branching_data n m u₀).1
  · rw [dataFlagQuotient, (dataFlagPartition n m).quotient_apply Role.flag Role.data
        (HeavyHexVertex.flag e₀) hflagCell]
    exact (branching_flag n m e₀).1
  · rw [dataFlagQuotient, (dataFlagPartition n m).quotient_apply Role.data Role.data
        (HeavyHexVertex.data u₀) hdataCell]
    exact (branching_data n m u₀).2
  · rw [dataFlagQuotient, (dataFlagPartition n m).quotient_apply Role.flag Role.flag
        (HeavyHexVertex.flag e₀) hflagCell]
    exact (branching_flag n m e₀).2

/-- The data cell has cardinality `N = |HoneyVertex n m|`. -/
theorem cellCard_data (n m : ℕ) :
    (dataFlagPartition n m).cellCard Role.data = (Fintype.card (HoneyVertex n m) : ℝ) := by
  classical
  unfold EquitablePartition.cellCard
  congr 1
  rw [show (Finset.univ.filter (fun w : HeavyHexVertex n m =>
        (dataFlagPartition n m).cells w = Role.data))
      = Finset.univ.image HeavyHexVertex.data by
    ext x; rcases x with v | e <;>
      simp [dataFlagPartition, role, HeavyHexVertex.data.injEq]]
  rw [Finset.card_image_of_injective _ (fun a b h => by injection h)]
  rfl

/-- The flag cell has cardinality `N·(N−1) = |HoneyDart n m|`. -/
theorem cellCard_flag (n m : ℕ) :
    (dataFlagPartition n m).cellCard Role.flag = (Fintype.card (HoneyDart n m) : ℝ) := by
  classical
  unfold EquitablePartition.cellCard
  congr 1
  rw [show (Finset.univ.filter (fun w : HeavyHexVertex n m =>
        (dataFlagPartition n m).cells w = Role.flag))
      = Finset.univ.image HeavyHexVertex.flag by
    ext x; rcases x with v | e <;>
      simp [dataFlagPartition, role, HeavyHexVertex.flag.injEq]]
  rw [Finset.card_image_of_injective _ (fun a b h => by injection h)]
  rfl

/-- A concrete honeycomb dart when `0 < n`, `0 < m` (its endpoints differ in the
sublattice bit). -/
def someDart (n m : ℕ) (hn : 0 < n) (hm : 0 < m) : HoneyDart n m :=
  ⟨((⟨0, hn⟩, ⟨0, hm⟩, false), (⟨0, hn⟩, ⟨0, hm⟩, true)), by simp⟩

/-- Both cells of the data/flag partition are nonempty when `0 < n`, `0 < m`.
This is the `hne` hypothesis required by `EquitablePartition.pst_lift`. -/
theorem dataFlag_cells_nonempty (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    ∀ k : Role, (dataFlagPartition n m).cellCard k ≠ 0 := by
  intro k; cases k with
  | data =>
    rw [cellCard_data]
    have : 0 < Fintype.card (HoneyVertex n m) :=
      Fintype.card_pos_iff.mpr ⟨(⟨0, hn⟩, ⟨0, hm⟩, false)⟩
    exact_mod_cast this.ne'
  | flag =>
    rw [cellCard_flag]
    have : 0 < Fintype.card (HoneyDart n m) :=
      Fintype.card_pos_iff.mpr ⟨someDart n m hn hm⟩
    exact_mod_cast this.ne'

/-- The number of honeycomb darts is `N·(N−1)` with `N = |HoneyVertex|`: ordered
distinct pairs are all `N²` ordered pairs minus the `N` diagonal pairs. -/
theorem card_darts (n m : ℕ) :
    Fintype.card (HoneyDart n m)
      = Fintype.card (HoneyVertex n m) * (Fintype.card (HoneyVertex n m) - 1) := by
  classical
  have hdiag : Fintype.card {p : HoneyVertex n m × HoneyVertex n m // p.1 = p.2}
      = Fintype.card (HoneyVertex n m) := by
    apply Fintype.card_congr
    refine ⟨fun p => p.val.1, fun v => ⟨(v, v), rfl⟩, ?_, fun v => rfl⟩
    rintro ⟨⟨a, b⟩, h⟩
    apply Subtype.ext
    simp only [Prod.mk.injEq, true_and]
    exact h
  have : Fintype.card (HoneyDart n m)
      = Fintype.card (HoneyVertex n m × HoneyVertex n m)
        - Fintype.card {p : HoneyVertex n m × HoneyVertex n m // p.1 = p.2} := by
    unfold HoneyDart
    exact Fintype.card_subtype_compl (fun p : HoneyVertex n m × HoneyVertex n m => p.1 = p.2)
  rw [this, hdiag, Fintype.card_prod, Nat.mul_sub_one]

/-- The symmetric (Hermitian) quotient `Q̃ = D^{1/2} Q D^{-1/2}` of the data/flag
partition is the off-diagonal `K_2`-like matrix `[[0, q],[q, 0]]` with the single
coupling `q = 2√(N−1)` (`N = |HoneyVertex| = 2nm`).  The diagonal vanishes.  This
is the concrete-realization analogue of the toroidal-template value `√6`. -/
theorem dataFlag_symmQuotient_form (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    (dataFlagPartition n m).symmQuotient Role.flag Role.data
        = (2 * Real.sqrt ((Fintype.card (HoneyVertex n m) : ℝ) - 1) : ℝ) ∧
      (dataFlagPartition n m).symmQuotient Role.data Role.data = 0 ∧
      (dataFlagPartition n m).symmQuotient Role.flag Role.flag = 0 := by
  classical
  have htf := dataFlagQuotient_toroidal_form n m hn hm
  have hNpos : 0 < Fintype.card (HoneyVertex n m) :=
    Fintype.card_pos_iff.mpr ⟨(⟨0, hn⟩, ⟨0, hm⟩, false)⟩
  have hN1 : (1 : ℝ) ≤ (Fintype.card (HoneyVertex n m) : ℝ) := by exact_mod_cast hNpos
  refine ⟨?_, ?_, ?_⟩
  · -- Q̃(flag,data) = √|flag| · Q(flag,data) / √|data| = √(N(N-1))·2/√N = 2√(N-1).
    unfold EquitablePartition.symmQuotient
    rw [show (dataFlagPartition n m).quotient Role.flag Role.data = 2 from htf.2.1,
        cellCard_flag, cellCard_data, card_darts]
    set N := Fintype.card (HoneyVertex n m)
    have hNR : (0:ℝ) < N := by exact_mod_cast hNpos
    have hNm1 : (0:ℝ) ≤ (N : ℝ) - 1 := by linarith
    -- √(N(N-1)) = √N · √(N-1)
    have hsplit : Real.sqrt ((N * (N - 1) : ℕ) : ℝ)
        = Real.sqrt (N : ℝ) * Real.sqrt ((N : ℝ) - 1) := by
      rw [show ((N * (N - 1) : ℕ) : ℝ) = (N : ℝ) * ((N : ℝ) - 1) by
        push_cast [Nat.cast_sub hNpos]; ring]
      rw [Real.sqrt_mul (le_of_lt hNR)]
    rw [hsplit]
    have hsqN : Real.sqrt (N : ℝ) ≠ 0 := by positivity
    have hsqNC : (Real.sqrt (N : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsqN
    push_cast
    field_simp
  · unfold EquitablePartition.symmQuotient
    rw [show (dataFlagPartition n m).quotient Role.data Role.data = 0 from htf.2.2.1]
    simp
  · unfold EquitablePartition.symmQuotient
    rw [show (dataFlagPartition n m).quotient Role.flag Role.flag = 0 from htf.2.2.2]
    simp

/-! ### Exact `2×2` Pauli-`X` diagonalization of the symmetric quotient.

The symmetric data/flag quotient is the off-diagonal `K_2` matrix
`M = [[0, q], [q, 0]] = q·X` (on the two-element index type `Role`), with the
single real coupling `q = 2√(N−1)`.  We diagonalize it *directly on `Role`* with
the Hadamard-type conjugator `Ur = [[1,1],[1,-1]]`, mirroring the `Fin 2`
treatment in `Integrations.QuantumAdvantage`, so that the matrix exponential
`exp(c·M)` has the closed form `cosh`/`sinh` and its off-diagonal modulus is
`|sinh(cq)|`.  This is what powers the PST and uniform-mixing payoffs below. -/

section RoleDiag

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- A sum over `Role` is the sum of its two values. -/
theorem Role.sum_univ {M : Type*} [AddCommMonoid M] (f : Role → M) :
    (∑ r : Role, f r) = f Role.data + f Role.flag := by
  rw [Fintype.sum_eq_add Role.data Role.flag (by decide) (by intro r hr; cases r <;> simp_all)]

open Complex in
/-- The `(data, flag)` entry of the symmetric quotient equals the `(flag, data)`
entry `q = 2√(N−1)` (the matrix is real-symmetric Hermitian). -/
theorem symmQuotient_dataFlag (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    (dataFlagPartition n m).symmQuotient Role.data Role.flag
      = (2 * Real.sqrt ((Fintype.card (HoneyVertex n m) : ℝ) - 1) : ℝ) := by
  have hH := (dataFlagPartition n m).symmQuotient_isHermitian
  have hfd := (dataFlag_symmQuotient_form n m hn hm).1
  -- Hermitian: M(data,flag) = star (M(flag,data)) = star (real) = real.
  have := congrFun (congrFun hH.eq Role.data) Role.flag
  rw [Matrix.conjTranspose_apply] at this
  rw [← this, hfd, Complex.star_def, Complex.conj_ofReal]

/-- The conjugating (Hadamard-type) matrix on `Role`: `Ur = [[1,1],[1,-1]]`. -/
noncomputable def Ur : Matrix Role Role ℂ :=
  Matrix.of fun r s => match r, s with
    | Role.data, Role.data => 1
    | Role.data, Role.flag => 1
    | Role.flag, Role.data => 1
    | Role.flag, Role.flag => -1

private theorem Ur_mul_half : Ur * ((1/2 : ℂ) • Ur) = 1 := by
  ext i j
  rw [Matrix.mul_apply, Role.sum_univ]
  cases i <;> cases j <;>
    simp [Ur, Matrix.one_apply] <;> ring

private theorem Ur_isUnit : IsUnit Ur := by
  refine ⟨⟨Ur, (1/2 : ℂ) • Ur, Ur_mul_half, ?_⟩, rfl⟩
  ext i j
  rw [Matrix.mul_apply, Role.sum_univ]
  cases i <;> cases j <;>
    simp [Ur, Matrix.one_apply] <;> ring

private theorem Ur_inv : Ur⁻¹ = (1/2 : ℂ) • Ur :=
  Matrix.inv_eq_right_inv Ur_mul_half

/-- The diagonal matrix `diag(a, b)` on `Role` (value `a` on `data`, `b` on
`flag`). -/
noncomputable def roleDiag (a b : ℂ) : Matrix Role Role ℂ :=
  Matrix.diagonal (fun r => match r with | Role.data => a | Role.flag => b)

/-- `q • X` on `Role` (with `X = [[0,1],[1,0]]`) conjugates to `diag(q, -q)`:
`q • Xr = Ur · diag(q, -q) · Ur⁻¹`, where `Xr` is the off-diagonal `Role` swap. -/
private theorem symmQuotient_eq_conj_diag (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    (dataFlagPartition n m).symmQuotient
      = Ur * roleDiag
          (((2 * Real.sqrt ((Fintype.card (HoneyVertex n m) : ℝ) - 1) : ℝ) : ℂ))
          (-((2 * Real.sqrt ((Fintype.card (HoneyVertex n m) : ℝ) - 1) : ℝ) : ℂ)) * Ur⁻¹ := by
  have hform := dataFlag_symmQuotient_form n m hn hm
  have hdf := symmQuotient_dataFlag n m hn hm
  rw [Ur_inv]
  ext i j
  rw [Matrix.mul_apply, Role.sum_univ, Matrix.mul_apply, Matrix.mul_apply,
    Role.sum_univ, Role.sum_univ]
  cases i <;> cases j <;>
    simp only [Ur, roleDiag, Matrix.diagonal_apply, Matrix.of_apply, Matrix.smul_apply,
      smul_eq_mul, ite_true, ite_false, reduceCtorEq] <;>
    first
      | (rw [hform.1]; push_cast; ring)
      | (rw [hform.2.1]; push_cast; ring)
      | (rw [hform.2.2]; push_cast; ring)
      | (rw [hdf]; push_cast; ring)

/-- The matrix exponential of `c • symmQuotient` in closed (diagonalized) form:
`exp(c·M) = Ur · diag(exp(cq), exp(-cq)) · Ur⁻¹`. -/
theorem exp_smul_symmQuotient (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (c : ℂ) :
    NormedSpace.exp (c • (dataFlagPartition n m).symmQuotient)
      = Ur * roleDiag
          (NormedSpace.exp (c * ((2 * Real.sqrt ((Fintype.card (HoneyVertex n m) : ℝ) - 1) : ℝ) : ℂ)))
          (NormedSpace.exp (-(c * ((2 * Real.sqrt ((Fintype.card (HoneyVertex n m) : ℝ) - 1) : ℝ) : ℂ))))
        * Ur⁻¹ := by
  set q : ℂ := ((2 * Real.sqrt ((Fintype.card (HoneyVertex n m) : ℝ) - 1) : ℝ) : ℂ) with hq
  rw [symmQuotient_eq_conj_diag n m hn hm]
  -- pull the scalar through the conjugation: c • (Ur * D * Ur⁻¹) = Ur * (c • D) * Ur⁻¹.
  rw [show c • (Ur * roleDiag q (-q) * Ur⁻¹) = Ur * (c • roleDiag q (-q)) * Ur⁻¹ by
        rw [Matrix.mul_smul, Matrix.smul_mul]]
  rw [Matrix.exp_conj _ _ Ur_isUnit]
  congr 2
  rw [show (c • roleDiag q (-q)) = roleDiag (c * q) (-(c * q)) by
        unfold roleDiag
        rw [← Matrix.diagonal_smul]
        congr 1; funext r; cases r <;> simp [mul_comm c]]
  unfold roleDiag
  rw [Matrix.exp_diagonal, Pi.exp_def]
  congr 1; funext r; cases r <;> simp

/-- The off-diagonal `(flag, data)` entry of `exp(c·M)` is `sinh(cq)`. -/
theorem exp_smul_symmQuotient_flag_data (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (c : ℂ) :
    NormedSpace.exp (c • (dataFlagPartition n m).symmQuotient) Role.flag Role.data
      = (NormedSpace.exp (c * ((2 * Real.sqrt ((Fintype.card (HoneyVertex n m) : ℝ) - 1) : ℝ) : ℂ))
          - NormedSpace.exp (-(c * ((2 * Real.sqrt ((Fintype.card (HoneyVertex n m) : ℝ) - 1) : ℝ) : ℂ)))) / 2 := by
  rw [exp_smul_symmQuotient n m hn hm, Ur_inv]
  rw [Matrix.mul_apply, Role.sum_univ, Matrix.mul_apply, Matrix.mul_apply,
    Role.sum_univ, Role.sum_univ]
  simp only [Ur, roleDiag, Matrix.diagonal_apply, Matrix.of_apply, Matrix.smul_apply,
    smul_eq_mul, ite_true, ite_false, reduceCtorEq]
  ring

end RoleDiag

/-- **Eigenvalues of the heavy-hex quotient.**  For the concrete complete-site
subdivision the raw quotient is `[[0, 2(N−1)],[2, 0]]` and the (Hermitian)
symmetric quotient is `[[0, q],[q, 0]]` with `q = 2√(N−1)`; the characteristic
polynomial is `λ² − q² = 0`, so the cell-uniform eigenvalues are `±q = ±2√(N−1)`
(`N = |HoneyVertex| = 2nm`).  This corrects the toroidal-template value `±√6`.

An eigenvalue `lam` lies in the spectrum iff `det(lam·I − Q) = 0`, i.e.
`lam² − 4(N−1) = 0` (the `(data,flag)·(flag,data)` product is `2(N−1)·2`),
whose two roots are exactly `±2√(N−1)` since `(2√(N−1))² = 4(N−1)`. -/
theorem dataFlagQuotient_eigenvalues (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    ∀ lam : ℂ, lam ∈ spectrum ℂ (dataFlagQuotient n m) ↔
      lam = (2 * Real.sqrt ((Fintype.card (HoneyVertex n m) : ℝ) - 1) : ℝ) ∨
      lam = -(2 * Real.sqrt ((Fintype.card (HoneyVertex n m) : ℝ) - 1) : ℝ) := by
  classical
  intro lam
  -- Concrete entries of the raw quotient.
  obtain ⟨hDF, hFD, hDD, hFF⟩ := dataFlagQuotient_toroidal_form n m hn hm
  set N := Fintype.card (HoneyVertex n m) with hN
  set s : ℝ := Real.sqrt ((N : ℝ) - 1) with hs
  -- `s² = N − 1 ≥ 0`.
  have hNpos : 0 < N := Fintype.card_pos_iff.mpr ⟨(⟨0, hn⟩, ⟨0, hm⟩, false)⟩
  have hN1 : (0:ℝ) ≤ (N : ℝ) - 1 := by
    have : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hNpos;
    linarith
  have hssq : s ^ 2 = (N : ℝ) - 1 := by rw [hs, sq, Real.mul_self_sqrt hN1]
  -- Equivalence `Role ≃ Fin 2`, used to compute the 2×2 determinant.
  let e : Role ≃ Fin 2 :=
    { toFun := fun r => match r with | Role.data => 0 | Role.flag => 1
      invFun := fun i => if i = 0 then Role.data else Role.flag
      left_inv := by intro r; cases r <;> rfl
      right_inv := by intro i; fin_cases i <;> rfl }
  -- `lam ∈ spectrum ↔ ¬ IsUnit (lam•1 − Q) ↔ det (lam•1 − Q) = 0`.
  rw [spectrum.mem_iff, Matrix.algebraMap_eq_diagonal, Matrix.isUnit_iff_isUnit_det,
      isUnit_iff_ne_zero, not_not]
  rw [show ((algebraMap ℂ (Role → ℂ)) lam) = (fun _ : Role => lam) from by
        funext r; simp [Algebra.algebraMap_eq_smul_one]]
  -- Compute the determinant by reindexing to `Fin 2`.
  have hdet : (Matrix.diagonal (fun _ : Role => lam) - dataFlagQuotient n m).det
      = lam ^ 2 - (4 * ((N : ℝ) - 1) : ℝ) := by
    rw [← Matrix.det_reindex_self e]
    rw [Matrix.det_fin_two]
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sub_apply,
      Matrix.diagonal_apply]
    -- e.symm 0 = data, e.symm 1 = flag.
    have h00 : (e.symm 0) = Role.data := rfl
    have h11 : (e.symm 1) = Role.flag := rfl
    rw [h00, h11]
    rw [hDD, hFF, hDF, hFD]
    -- diagonal indicators
    simp only [if_pos rfl, reduceCtorEq, if_neg (by decide : ¬ Role.data = Role.flag),
      if_neg (by decide : ¬ Role.flag = Role.data)]
    push_cast [Nat.cast_sub hNpos]
    ring
  rw [hdet]
  -- `lam² = 4(N−1)` iff `lam = ±2√(N−1) = ±2s`.
  have hfactor : lam ^ 2 - (4 * ((N : ℝ) - 1) : ℝ) = 0 ↔
      lam = ((2 * s : ℝ) : ℂ) ∨ lam = (-(2 * s : ℝ) : ℂ) := by
    have hsc : ((4 * ((N : ℝ) - 1) : ℝ) : ℂ) = (((2 * s : ℝ)) : ℂ) ^ 2 := by
      push_cast
      rw [show (2 * (s:ℂ)) ^ 2 = 4 * (s:ℂ)^2 by ring]
      rw [show ((s:ℝ):ℂ)^2 = (((s^2 : ℝ)) : ℂ) by push_cast; ring, hssq]
      push_cast; ring
    rw [hsc, sub_eq_zero, sq_eq_sq_iff_eq_or_eq_neg]
  -- After folding `s = √(N−1)` the two sides coincide.
  rw [hfactor, hs]

/-! ### Heavy-hex as a `GraphBundle` (data-sublattice only).

*Motivation (the intended, not-yet-built structure).*  A faithful heavy-hex
bundle over the honeycomb template would give each honeycomb edge a 2-vertex
"subdivision fiber" (the inserted flag together with one of its endpoints), with
the honeycomb template edges realised as biregular `[1] × [1]` couplings.

**What is actually realized here is weaker.**  The `heavyHexAsBundle` below uses
**trivial `Unit` fibers**, so it carries no flag qubits and models *only the
data sublattice* (the honeycomb sites), not the subdivision graph.  We therefore
do **not** claim a bundle-level equivalence with `heavyHexWeighted`; the only
honest content is the *vertex* bijection onto the data sublattice
(`heavyHexAsBundle_dataVertex_equiv`).  A genuine flag-carrying subdivision
bundle (two-vertex fibers, as in the motivation) is left to future work. -/

/-- A `GraphBundle` over the honeycomb template with **trivial `Unit` fibers**.

HONEST SCOPE (the name over-promises).  This is **not** a faithful bundle model
of the heavy-hex chip.  Its fibers are `fun _ => Unit` — singletons that carry
**no** flag qubits — so the total space is just `Σ _ : HoneyVertex, Unit ≃
HoneyVertex` (the data sublattice), and the total adjacency is the honeycomb
*template join* on data sites, not the data–flag subdivision graph.  In
particular it does **not** agree with `heavyHexWeighted n m` (cardinalities
already differ: `N` vs `N + N(N−1)`), and we do **not** claim that equivalence.
The only honest content recovered is the *vertex* bijection onto the data
sublattice, stated and proved in `heavyHexAsBundle_dataVertex_equiv`.  A
flag-carrying realisation needs a genuine subdivision bundle (two-vertex
fibers), which is not developed here. -/
noncomputable def heavyHexAsBundle (n m : ℕ) :
    GraphBundle (HoneycombLattice n m) (fun _ => Unit) := by
  classical
  exact GraphBundle.ofTemplateJoin (HoneycombLattice n m) (fun _ => Unit)

/-- **Vertex bijection: the Unit-fiber bundle models exactly the DATA
sublattice.**  The total-vertex type of `heavyHexAsBundle` is
`Σ _ : HoneyVertex n m, Unit`, which has `N = |HoneyVertex|` elements — one per
honeycomb site.  This is in canonical bijection with the *data* vertices of the
heavy-hex chip, `{x : HeavyHexVertex n m // role x = Role.data}`, pairing each
`⟨v, ()⟩` with `data v`.

We state ONLY the vertex bijection, not an adjacency intertwining.  The
Unit-fiber bundle carries no flag qubits (its fibers are singletons, with no
dart-indexed sum), so it cannot recover the full `HeavyHexVertex n m` vertex
type (`N + N(N−1)` darts) — the previously-claimed full bijection was
*false as stated* (the cardinalities differ).  Moreover the bundle's total
adjacency is the *honeycomb template join* on data sites, whereas heavy-hex
data vertices are pairwise NON-adjacent (every chip edge is data–flag), so no
adjacency-intertwining holds either.  A faithful flag-carrying realisation
needs a genuine subdivision bundle, developed elsewhere. -/
theorem heavyHexAsBundle_dataVertex_equiv (n m : ℕ) :
    -- There is a vertex bijection between the bundle's total vertex type
    -- (`N` honeycomb sites) and the data sublattice of the chip.
    Nonempty ((Σ _ : HoneyVertex n m, Unit) ≃
      {x : HeavyHexVertex n m // role x = Role.data}) := by
  classical
  refine ⟨{
    toFun := fun p => ⟨HeavyHexVertex.data p.1, rfl⟩
    invFun := fun x => ⟨(match x with
      | ⟨HeavyHexVertex.data v, _⟩ => v
      | ⟨HeavyHexVertex.flag _, h⟩ => absurd h (by simp [role])), ()⟩
    left_inv := ?_
    right_inv := ?_ }⟩
  · rintro ⟨v, ⟨⟩⟩; rfl
  · rintro ⟨x, hx⟩
    cases x with
    | data v => rfl
    | flag e => exact absurd hx (by simp [role])

/-! ## 4. Walk primitives on the quotient.

We now state which CTQW primitives the quotient supports, and that they lift
to cell-uniform primitives on the chip.

(SCOPE: as flagged in the file header, the realized graph is the `K_N`-site
subdivision, so the raw quotient is `Q = [[0, 2(N−1)], [2, 0]]` and the
symmetric quotient is `Q̃ = [[0, q], [q, 0]]` with coupling `q = 2√(N−1)`.  The
`[[0, 3], …]` / `√6` honeycomb-template values written in the *illustrative*
list below are **not** the realized ones — they are the boundary-truncated
honeycomb template that this file does not build; substitute `q = 2√(N−1)`
throughout for the actual statements, which are the theorems that follow.)

Illustrative honeycomb-template form (NOT realized here), 2×2 quotient
`Q = [[0, 3], [2, 0]]`:

* **PST**: the symmetric symmetrization `Q̃ = [[0, √6], [√6, 0]]` has perfect
  state transfer at time `π / (2√6)` between the data-cell and the flag-cell.
  (Standard textbook example: `K_2` weighted by `√6`.)
* **Uniform mixing**: at time `t = π / (4√6)` the symmetric quotient
  evolves the data-uniform state to a 50/50 superposition of data and flag
  uniform states.
* **Search**: marking the data cell, the search Hamiltonian
  `-γ Q - P_{data}` on the quotient has spectral gap optimised at
  `γ = 1/√6`.

The *realized* `K_N` statements below carry `q = dataFlagCoupling n m =
2√(N−1)` (PST at `π/(2q)`, mixing at `π/(4q)`). -/

/-- The single coupling of the symmetric data/flag quotient, `q = 2√(N−1)`. -/
noncomputable def dataFlagCoupling (n m : ℕ) : ℝ :=
  2 * Real.sqrt ((Fintype.card (HoneyVertex n m) : ℝ) - 1)

/-- The coupling `q = 2√(N−1)` is strictly positive whenever `0 < n, 0 < m`
(then `N = |HoneyVertex| ≥ 2`, so `N − 1 ≥ 1 > 0`). -/
theorem dataFlagCoupling_pos (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    0 < dataFlagCoupling n m := by
  unfold dataFlagCoupling
  have hN : 2 ≤ Fintype.card (HoneyVertex n m) := by
    have hcard : Fintype.card (HoneyVertex n m) = n * (m * 2) := by
      simp only [HoneyVertex, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
    rw [hcard]
    have h1 : 1 ≤ n := hn
    have h2 : 1 ≤ m := hm
    calc 2 = 1 * (1 * 2) := by norm_num
      _ ≤ n * (m * 2) := by
          apply Nat.mul_le_mul h1
          exact Nat.mul_le_mul h2 (le_refl 2)
  have h1 : (1 : ℝ) ≤ (Fintype.card (HoneyVertex n m) : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (Fintype.card (HoneyVertex n m) : ℝ) := by exact_mod_cast hN
    linarith
  have : 0 < Real.sqrt ((Fintype.card (HoneyVertex n m) : ℝ) - 1) :=
    Real.sqrt_pos.mpr (by linarith)
  positivity

/-- **Closed-form off-diagonal modulus of the symmetric-quotient walk.**  For real
time `τ`, the `(flag, data)` matrix element of `exp(-i τ M)` (`M = q·X`,
`q = 2√(N−1)`) is `-i·sin(τ q)`, of modulus `|sin(τ q)|`.  This is the genuine
two-cell Rabi oscillation underlying both PST and uniform mixing on the chip. -/
theorem norm_exp_symmQuotient_flag_data (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (τ : ℝ) :
    ‖(NormedSpace.exp (-(Complex.I * (τ : ℂ)) •
        (dataFlagPartition n m).symmQuotient)) Role.flag Role.data‖
      = |Real.sin (τ * dataFlagCoupling n m)| := by
  rw [exp_smul_symmQuotient_flag_data n m hn hm]
  set q : ℝ := 2 * Real.sqrt ((Fintype.card (HoneyVertex n m) : ℝ) - 1) with hqdef
  -- the scalar `c = -(I τ)`, so `c·q = -(I τ q)`.
  -- Identify the argument `-(I τ) · q` with `(-(τ q)) · I` (real-times-I form).
  have hsval : (-(Complex.I * (τ : ℂ)) * ((q : ℝ) : ℂ)) = ((-(τ * q) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  have he1 : NormedSpace.exp (-(Complex.I * (τ : ℂ)) * ((q : ℝ) : ℂ))
      = (Real.cos (-(τ*q)) : ℂ) + (Real.sin (-(τ*q)) : ℂ) * Complex.I := by
    rw [hsval, ← Complex.exp_eq_exp_ℂ, Complex.exp_ofReal_mul_I]
  have he2 : NormedSpace.exp (-(-(Complex.I * (τ : ℂ)) * ((q : ℝ) : ℂ)))
      = (Real.cos (τ*q) : ℂ) + (Real.sin (τ*q) : ℂ) * Complex.I := by
    have hneg : -(-(Complex.I * (τ : ℂ)) * ((q : ℝ) : ℂ)) = ((τ * q : ℝ) : ℂ) * Complex.I := by
      rw [hsval]; push_cast; ring
    rw [hneg, ← Complex.exp_eq_exp_ℂ, Complex.exp_ofReal_mul_I]
  rw [he1, he2, Real.cos_neg, Real.sin_neg]
  rw [show ((Real.cos (τ*q) : ℂ) + ((-Real.sin (τ*q) : ℝ) : ℂ) * Complex.I
        - ((Real.cos (τ*q) : ℂ) + (Real.sin (τ*q) : ℂ) * Complex.I)) / 2
      = -Complex.I * (Real.sin (τ*q) : ℂ) by push_cast; ring]
  rw [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [hqdef, dataFlagCoupling]

/-- **PST on the data/flag quotient at time `π / (2q)`, `q = 2√(N−1)`.**  This is
the analytically-tractable two-cell PST that the heavy-hex chip supports
*automatically* via the equitable-partition lift.  (The toroidal-template value
would put `q = √6`; the concrete complete-site subdivision has `q = 2√(N−1)`.)

Fully proved (no `sorry`): the symmetric quotient is exactly `q·X` (off-diagonal
`K_2`), whose evolution off-diagonal modulus is `|sin(qτ)|` by
`norm_exp_symmQuotient_flag_data`; at `τ = π/(2q)` this is `sin(π/2) = 1`. -/
theorem dataFlag_pst_on_quotient (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    ∃ τ : ℝ, τ = Real.pi / (2 * dataFlagCoupling n m) ∧
      ‖(NormedSpace.exp (-(Complex.I * (τ : ℂ)) •
          (dataFlagPartition n m).symmQuotient)) Role.flag Role.data‖ = 1 := by
  refine ⟨Real.pi / (2 * dataFlagCoupling n m), rfl, ?_⟩
  rw [norm_exp_symmQuotient_flag_data n m hn hm]
  have hq : dataFlagCoupling n m ≠ 0 := (dataFlagCoupling_pos n m hn hm).ne'
  rw [show Real.pi / (2 * dataFlagCoupling n m) * dataFlagCoupling n m
        = Real.pi / 2 by field_simp]
  rw [Real.sin_pi_div_two, abs_one]

/-- **Uniform mixing on the data/flag quotient at time `π / (4q)`, `q = 2√(N−1)`.**
At this time the symmetric quotient walk sends the data-uniform state to a 50/50
data/flag superposition: `‖U(t)_{flag,data}‖ = |sin(qt)| = 1/√2`.

Fully proved (no `sorry`): the off-diagonal modulus `|sin(qt)|` comes from the
closed form `norm_exp_symmQuotient_flag_data`, and at `t = π/(4q)` this is
`sin(π/4) = 1/√2`. -/
theorem dataFlag_uniform_mixing_on_quotient (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    ∃ t : ℝ, t = Real.pi / (4 * dataFlagCoupling n m) ∧
      ‖(NormedSpace.exp (-(Complex.I * (t : ℂ)) •
          (dataFlagPartition n m).symmQuotient)) Role.flag Role.data‖
        = 1 / Real.sqrt 2 := by
  refine ⟨Real.pi / (4 * dataFlagCoupling n m), rfl, ?_⟩
  rw [norm_exp_symmQuotient_flag_data n m hn hm]
  have hq : dataFlagCoupling n m ≠ 0 := (dataFlagCoupling_pos n m hn hm).ne'
  rw [show Real.pi / (4 * dataFlagCoupling n m) * dataFlagCoupling n m
        = Real.pi / 4 by field_simp]
  rw [Real.sin_pi_div_four, abs_of_nonneg (by positivity)]
  rw [eq_div_iff (by positivity), div_mul_eq_mul_div, Real.mul_self_sqrt (by norm_num)]
  norm_num

/-! ### IBM tunable-coupler as a chiral-signing channel.

IBM Heron introduced *tunable couplers*: each two-qubit physical coupling
carries a programmable phase φ ∈ [0, 2π].  In the Graphplay language this is
exactly the **chiral-signing** primitive of `Graphplay.Chiral`: the tunable
coupler implements a `ChiralSigning V` whose values are restricted to a
discrete (analog-controllable) subset of the unit circle.

In particular, IBM hardware allows *cross-constant* chiral signings whose
phase depends only on the data/flag cell pair — those are exactly the
chirals that descend to a quotient phasing by
`WeightedGraph.signedBy_preserves_equitable`. -/

/-- The set of phases realisable on an IBM Heron tunable coupler.  Modelled
abstractly as the full unit circle for now; the real chip supports an analog
range of phases discretised by the control hardware. -/
noncomputable def heronAllowedPhases : Set ℂ :=
  { z : ℂ | ‖z‖ = 1 }

/-- A chiral signing of the heavy-hex chip whose phases depend only on the
data/flag cell pair.  By `Chiral.WeightedGraph.signedBy_preserves_equitable`
this descends to a 2 x 2 chiral phasing of the quotient. -/
noncomputable def heronChiralSigning (n m : ℕ)
    (τ : Role → Role → ℂ)
    (hτ : ∀ r s, ‖τ r s‖ = 1)
    (hτh : ∀ r s, τ s r = star (τ r s))
    (hτd : ∀ r, τ r r = 1) :
    ChiralSigning (HeavyHexVertex n m) where
  σ x y := τ (role x) (role y)
  unimod := by intro x y; exact hτ (role x) (role y)
  herm := by intro x y; exact hτh (role x) (role y)
  diag := by intro x; exact hτd (role x)

/-- The Heron chiral signing is cross-constant on the data/flag partition by
construction. -/
theorem heronChiralSigning_crossConstant
    (n m : ℕ) (τ : Role → Role → ℂ)
    (hτ : ∀ r s, ‖τ r s‖ = 1)
    (hτh : ∀ r s, τ s r = star (τ r s))
    (hτd : ∀ r, τ r r = 1) :
    (heronChiralSigning n m τ hτ hτh hτd).CrossConstant
      (dataFlagPartition n m).cells := by
  refine ⟨τ, ?_⟩
  intro x y
  rfl

/-! ## 5. Lift theorems.

These are *instances* of the generic lifting theorems in
`Graphplay.PST`, `Graphplay.Mixing`, and `Graphplay.Search` applied to the
data/flag partition.  Each one converts a quotient-side guarantee into a
cell-uniform guarantee on the heavy-hex chip. -/

/-- **PST lift.**  PST on the 2 x 2 data/flag quotient at time `π / (2q)`
(`q = 2√(N−1)`) lifts to cell-uniform PST between the data-uniform state and
the flag-uniform state on the chip.  This is a genuine application of
`EquitablePartition.pst_lift`: the cells are nonempty
(`dataFlag_cells_nonempty`) and the quotient-side unit-modulus amplitude is
`dataFlag_pst_on_quotient`. -/
theorem heavyHex_pst_lift (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    IsCellUniformPST (heavyHexWeighted n m) (dataFlagPartition n m)
      Role.data Role.flag (Real.pi / (2 * dataFlagCoupling n m)) := by
  obtain ⟨τ, hτ, hpst⟩ := dataFlag_pst_on_quotient n m hn hm
  rw [← hτ]
  exact (dataFlagPartition n m).pst_lift (dataFlag_cells_nonempty n m hn hm) hpst

/-- **Uniform-mixing lift (genuine cell-block form).**  At time `t = π/(4q)`
(`q = 2√(N−1)`) the heavy-hex *base* walk sends the data-uniform state to a
50/50 data/flag superposition: the off-diagonal data↔flag cell-block amplitude
has modulus-squared exactly `|C_data|·|C_flag|/2`.

This is the genuine cell-block mixing identity that lifts from
`dataFlag_uniform_mixing_on_quotient` (the quotient walk's off-diagonal modulus
is `|sin(qt)| = 1/√2`) via the *proven* intertwining
`cellUniform_matrixElement` + `exp_smul_adj_mul_cellEmbed`: the cell-block
amplitude `cellBlockAmp P (evolve t) i j` equals
`exp(-iτQ̃)_{ij}·√|C_i|·√|C_j|`, so its modulus-squared is
`(1/2)·|C_data|·|C_flag|`.

CORRECTNESS FIX (replaces a *false* prior statement): the generic
`IsCellUniformMixing` predicate demands the `1/N²` Born normalization with
`N = |HeavyHexVertex|`; for a coarse **2-cell** quotient the off-diagonal
amplitude-squared is `|C_i||C_j|/2`, and unitarity of the `2×2` quotient
evolution (`∑_j‖exp_{ij}‖² = 1` over only two cells) forces `2/N² = 1`, i.e.
`N = √2` — impossible.  So `IsCellUniformMixing … (π/(4q))` is *not* a theorem
for the heavy-hex; the genuine, non-vacuous content is the cell-block modulus
identity proved here. -/
theorem heavyHex_mixing_cellBlock (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    ‖cellBlockAmp (dataFlagPartition n m)
        ((heavyHexWeighted n m).evolve (Real.pi / (4 * dataFlagCoupling n m)))
        Role.flag Role.data‖ ^ 2
      = (dataFlagPartition n m).cellCard Role.flag
          * (dataFlagPartition n m).cellCard Role.data / 2 := by
  classical
  set P := dataFlagPartition n m with hP
  set t : ℝ := Real.pi / (4 * dataFlagCoupling n m) with ht
  set s : ℂ := -(Complex.I * (t : ℂ)) with hs
  -- Cell cardinalities are nonzero (both cells nonempty).
  have hne := dataFlag_cells_nonempty n m hn hm
  have hfi : P.cellCard Role.flag ≠ 0 := hne Role.flag
  have hdi : P.cellCard Role.data ≠ 0 := hne Role.data
  have hsf : (Real.sqrt (P.cellCard Role.flag) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]
    exact ne_of_gt (Real.sqrt_pos.mpr (lt_of_le_of_ne (P.cellCard_nonneg _) (Ne.symm hfi)))
  have hsd : (Real.sqrt (P.cellCard Role.data) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]
    exact ne_of_gt (Real.sqrt_pos.mpr (lt_of_le_of_ne (P.cellCard_nonneg _) (Ne.symm hdi)))
  -- `cellBlockAmp = (Bᴴ * evolve t * B)_{flag,data} · √|C_data|·√|C_flag|`,
  -- via `cellUniform_matrixElement` with indices (data, flag) and the swap that
  -- already appears in `cellBlockAmp_eq_quotient`.
  have hswap : cellBlockAmp P ((heavyHexWeighted n m).evolve t) Role.flag Role.data
      = ∑ x, ∑ y, if P.cells x = Role.data ∧ P.cells y = Role.flag
          then (heavyHexWeighted n m).evolve t y x else 0 := by
    unfold cellBlockAmp
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun x _ => ?_))
    by_cases h : P.cells x = Role.flag ∧ P.cells y = Role.data
    · rw [if_pos h, if_pos ⟨h.2, h.1⟩]
    · rw [if_neg h, if_neg (fun hc => h ⟨hc.2, hc.1⟩)]
  -- The intertwining `Bᴴ · evolve t · B = exp(s • symmQuotient)`.
  have hev : (heavyHexWeighted n m).evolve t = NormedSpace.exp (s • (heavyHexWeighted n m).adj) :=
    rfl
  have hEB : (heavyHexWeighted n m).evolve t * P.cellEmbed
      = P.cellEmbed * NormedSpace.exp (s • P.symmQuotient) := by
    rw [hev]; exact P.exp_smul_adj_mul_cellEmbed s
  have hBEB : (P.cellEmbedᴴ * (heavyHexWeighted n m).evolve t * P.cellEmbed)
      = NormedSpace.exp (s • P.symmQuotient) := by
    rw [Matrix.mul_assoc, hEB, ← Matrix.mul_assoc,
      P.cellEmbed_conjTranspose_mul_cellEmbed hne, Matrix.one_mul]
  -- Plug into `cellUniform_matrixElement` (i = data, j = flag).
  have hme := P.cellUniform_matrixElement ((heavyHexWeighted n m).evolve t) Role.data Role.flag
  rw [hBEB] at hme
  -- `cellBlockAmp = exp(s•Q̃)_{flag,data} · (√|C_data|·√|C_flag|)`.
  have hcb : cellBlockAmp P ((heavyHexWeighted n m).evolve t) Role.flag Role.data
      = NormedSpace.exp (s • P.symmQuotient) Role.flag Role.data
          * ((Real.sqrt (P.cellCard Role.data) : ℂ) * (Real.sqrt (P.cellCard Role.flag) : ℂ)) := by
    rw [hswap, ← hme, div_mul_cancel₀]
    exact mul_ne_zero hsd hsf
  -- Take moduli and square.  The quotient off-diagonal modulus is `1/√2`.
  have hquotmod : ‖NormedSpace.exp (s • P.symmQuotient) Role.flag Role.data‖ = 1 / Real.sqrt 2 := by
    obtain ⟨t', ht', hmix⟩ := dataFlag_uniform_mixing_on_quotient n m hn hm
    rw [← ht] at ht'
    rw [hs, ← ht']
    exact hmix
  rw [hcb, norm_mul, norm_mul, hquotmod, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)]
  -- `(1/√2 · √|C_data| · √|C_flag|)² = |C_data|·|C_flag|/2 = |C_flag|·|C_data|/2`.
  rw [mul_pow, mul_pow, div_pow, one_pow,
    Real.sq_sqrt (le_of_lt (lt_of_le_of_ne (P.cellCard_nonneg _) (Ne.symm hdi))),
    Real.sq_sqrt (le_of_lt (lt_of_le_of_ne (P.cellCard_nonneg _) (Ne.symm hfi))),
    Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  ring

/-- **Search lift (genuine conditional form).**  Marking a *cell-union* set `M`
(membership constant on each data/flag role-cell, hypothesis `hM`) and assuming
the marked-refined data/flag **quotient** itself supports optimal search
(`IsRefinedQuotientOptimalSearch`), the host heavy-hex chip supports optimal
search at the same `(γ, τ)`.

FALSE→TRUE MIGRATION (the prior statement was *false as stated*).  The earlier
version asserted `IsOptimalSearch (heavyHexWeighted n m) M γ τ` for **arbitrary**
`γ, τ, M` — i.e. that the heavy-hex achieves the `≥ 1/√2` marked-amplitude bound
unconditionally.  Counterexample: take `τ = 0`, so `searchEvolve M γ 0 =
exp(0) = 1` (identity); then the success amplitude is
`‖∑_v ∑_{m∈M} (if v = m then 1 else 0)/√(card V)‖ = |M| / √(card V)`, which for a
single marked qubit (`|M| = 1`) on any chip with `card V > 2` is `< 1/√2`.  So the
unconditional claim is refuted.  The genuine content — and what the spectral
disassembly actually buys — is the *lift*: optimal search on the small refined
quotient transfers to the chip.  We expose it as the honest hypothesis
`IsRefinedQuotientOptimalSearch`.

The hypotheses are jointly satisfiable and non-vacuous: with `M` the data cell,
`hM` holds (data-membership is constant on each role-cell), and for the standard
Childs–Goldstone resonant `(γ, τ)` the refined `2×2`-quotient search reaches the
`1/√2` amplitude, witnessing `IsRefinedQuotientOptimalSearch`.

HONEST `sorry` on a TRUE statement.  The bridge is the upstream
`EquitablePartition.optimal_search_lift` (host search Hamiltonian acts as the
refined-quotient one on the cell-uniform subspace, via `search_quotient_reduction`
+ cell-inflate norm preservation).  That upstream lift is itself an honest
theorem-level `sorry`, *and* its `hne : ∀ i, 0 < (refineByMarked).cellCard i`
hypothesis is too strong to invoke here — under `hM` every parent role-cell is
entirely in or out of `M`, so one of its two refined sub-cells is empty and
`hne` cannot hold for *both* sub-cells.  Re-deriving the lift with the
genuinely-needed *marked-side-only* nonemptiness is the deferred step; we keep an
honest `sorry` on this TRUE, non-vacuous conditional rather than route through the
vacuous `hne`. -/
theorem heavyHex_search_lift (n m : ℕ) (γ τ : ℝ)
    (M : Finset (HeavyHexVertex n m))
    (hM : ∀ x y : HeavyHexVertex n m,
        (dataFlagPartition n m).cells x = (dataFlagPartition n m).cells y →
          (x ∈ M ↔ y ∈ M))
    (hquot : IsRefinedQuotientOptimalSearch (dataFlagPartition n m) M hM γ τ) :
    IsOptimalSearch (heavyHexWeighted n m) M γ τ := by
  -- Reduce via `search_quotient_reduction` to the marked-refined data/flag
  -- quotient and apply the (marked-side) optimal-search lift.
  -- HONEST sorry: upstream `optimal_search_lift` reduction, restated to avoid the
  -- vacuous all-sub-cell-nonempty `hne` (see docstring).
  sorry

/-- **Chiral-mixing lift.**  Any *cross-constant* chiral signing of heavy-hex
descends to a 2 x 2 chiral phasing of the quotient; cell-uniform mixing of
the signed chip is equivalent to uniform mixing of the signed quotient.

Stated existentially over the cross-constant witness to dodge the
`let`-binding in the type.

⚠ CONDITIONAL / `sorry`-DEPENDENT.  This is a direct instance of
`Bundle.chiral_mixing_optimization`, whose proof is an honest theorem-level
`sorry` (the characteristic-isometry intertwining `S* U(t) S = U_quot(t)` is
deferred upstream).  So this theorem inherits `sorryAx`; it is NOT a clean
`#print axioms`-verified result.  Treat it as the statement of the lift,
contingent on the upstream chiral-optimization theorem. -/
theorem heavyHex_chiral_mixing_lift (n m : ℕ)
    (τ : Role → Role → ℂ)
    (hτ : ∀ r s, ‖τ r s‖ = 1)
    (hτh : ∀ r s, τ s r = star (τ r s))
    (hτd : ∀ r, τ r r = 1) (t : ℝ) :
    ∃ (B : Bundle (HeavyHexVertex n m) Role)
      (s : ChiralSigning (HeavyHexVertex n m))
      (h : s.CrossConstant B.partition.cells),
      -- cell-uniform mixing of the signed chip ⇔ the signed (symmetric)
      -- quotient walk has equal-modulus columns (the genuine RHS of
      -- `Bundle.chiral_mixing_optimization`).
      ((B.signedBy s h).CellUniformMixing t ↔
        (∀ k k' l : Role,
          ‖(NormedSpace.exp (-(Complex.I * (t : ℂ)) •
              (B.signedBy s h).partition.symmQuotient)) l k‖
            = ‖(NormedSpace.exp (-(Complex.I * (t : ℂ)) •
              (B.signedBy s h).partition.symmQuotient)) l k'‖)) := by
  -- Direct application of `Bundle.chiral_mixing_optimization`.
  exact ⟨⟨heavyHexWeighted n m, dataFlagPartition n m⟩,
          heronChiralSigning n m τ hτ hτh hτd,
          heronChiralSigning_crossConstant n m τ hτ hτh hτd,
          Bundle.chiral_mixing_optimization _ _ _ t⟩

/-! ## 6. Hardware spec extraction.

We assemble a `HardwareSpec` matching the public specs of IBM Eagle and
Heron processors. -/

/-- The IBM Eagle hardware spec: planar layout (genus 0), 127 qubits,
nearest-neighbour couplings (no long-range edges), real-coefficient
couplings (no tunable coupler ⇒ phase set `{1}` only), no degree
constraint (boundary effects break regularity). -/
noncomputable def ibmEagleSpec : HardwareSpec where
  maxCouplingDistance := some 1
  surfaceGenus := some 0
  qubitCountBound := some 127
  allowedPhaseSet := { (1 : ℂ) }
  requiredRegularity := none

/-- The IBM Heron hardware spec.  The improvements over Eagle are:

* tunable couplers ⇒ analog phase control, so `allowedPhaseSet = unit
  circle` instead of `{1}`;
* slightly larger size (133 qubits);
* otherwise the same planar, nearest-neighbour heavy-hex skeleton. -/
noncomputable def ibmHeronSpec : HardwareSpec where
  maxCouplingDistance := some 1
  surfaceGenus := some 0
  qubitCountBound := some 133
  allowedPhaseSet := heronAllowedPhases
  requiredRegularity := none

/-- The IBM Condor hardware spec.  Same skeleton, much larger qubit count.
Condor was an *engineering demonstrator* without high-fidelity gates; we
list it for completeness. -/
noncomputable def ibmCondorSpec : HardwareSpec where
  maxCouplingDistance := some 1
  surfaceGenus := some 0
  qubitCountBound := some 1121
  allowedPhaseSet := heronAllowedPhases
  requiredRegularity := none

/-- **Phase/topology fit of the Eagle chip (qubit-count bound dropped).**

This is the HONEST, non-vacuous fit claim.  The full-dart vertex model has
`|HeavyHexVertex 7 18| = N + N(N−1)` darts (`N = 252`), which is `≫ 127` — so
the chip does *not* satisfy the literal `qubitCountBound = some 127` conjunct of
`ibmEagleSpec` (the previously-claimed `heavyHexEagle_satisfies` was *false as
stated*: the full dart space is not the physical qubit count).  Matching the
real 127-qubit count requires a hardware-*truncation subset* model (the actual
qubit subset of the dart space), which is not developed in this file.

What IS true, and is proved here, is everything *except* the size bound: with
`qubitCountBound` dropped to `none`, the Eagle chip satisfies its spec — in
particular the genuinely-enforced **allowed-phase** conjunct (`{1}`, since
heavy-hex weights are `0/1`). -/
theorem heavyHexEagle_satisfies_dropCount (embed : HeavyHexVertex 7 18 → ℝ × ℝ) :
    heavyHexEagle.satisfies { ibmEagleSpec with qubitCountBound := none } embed := by
  refine ⟨fun _ _ _ => trivial, trivial, trivial, ?_, trivial⟩
  intro x y hxy
  -- heavy-hex weights are `0/1`; a nonzero weight is `1 ∈ {1}`.
  show heavyHexEagle.adj x y ∈ ({(1 : ℂ)} : Set ℂ)
  have hval : heavyHexEagle.adj x y = 1 := by
    unfold heavyHexEagle heavyHexWeighted Graphplay.SimpleGraph.toWeighted at hxy ⊢
    by_cases h : (HeavyHexLattice 7 18).Adj x y
    · simp [_root_.SimpleGraph.adjMatrix_apply, h]
    · simp [_root_.SimpleGraph.adjMatrix_apply, h] at hxy
  simp [hval]

/-- **Phase/topology fit of the Heron chip (qubit-count bound dropped).**

Same honest caveat as `heavyHexEagle_satisfies_dropCount`:
`|HeavyHexVertex 7 19| ≫ 133`, so the literal count conjunct of `ibmHeronSpec`
is *false* on the full dart model — a truncation-subset model is needed for the
real 133-qubit count.  With the count bound dropped, the chip satisfies its
spec, including the genuinely-enforced allowed-phase conjunct (`heronAllowedPhases
= unit circle`, and `‖(1:ℂ)‖ = 1`). -/
theorem heavyHexHeron_satisfies_dropCount (embed : HeavyHexVertex 7 19 → ℝ × ℝ) :
    heavyHexHeron.satisfies { ibmHeronSpec with qubitCountBound := none } embed := by
  refine ⟨fun _ _ _ => trivial, trivial, trivial, ?_, trivial⟩
  intro x y hxy
  show heavyHexHeron.adj x y ∈ heronAllowedPhases
  have hval : heavyHexHeron.adj x y = 1 := by
    unfold heavyHexHeron heavyHexWeighted Graphplay.SimpleGraph.toWeighted at hxy ⊢
    by_cases h : (HeavyHexLattice 7 19).Adj x y
    · simp [_root_.SimpleGraph.adjMatrix_apply, h]
    · simp [_root_.SimpleGraph.adjMatrix_apply, h] at hxy
  simp only [hval, heronAllowedPhases, Set.mem_setOf_eq, norm_one]

/-- **Phase/topology fit of the Condor chip (qubit-count bound dropped).**

Same honest caveat as `heavyHexEagle_satisfies_dropCount`:
`|HeavyHexVertex 33 34| ≫ 1121`, so the literal count conjunct of `ibmCondorSpec`
is *false* on the full dart model — a truncation-subset model is needed for the
real 1121-qubit count.  With the count bound dropped, the chip satisfies its
spec, including the genuinely-enforced allowed-phase conjunct. -/
theorem heavyHexCondor_satisfies_dropCount (embed : HeavyHexVertex 33 34 → ℝ × ℝ) :
    heavyHexCondor.satisfies { ibmCondorSpec with qubitCountBound := none } embed := by
  refine ⟨fun _ _ _ => trivial, trivial, trivial, ?_, trivial⟩
  intro x y hxy
  show heavyHexCondor.adj x y ∈ heronAllowedPhases
  have hval : heavyHexCondor.adj x y = 1 := by
    unfold heavyHexCondor heavyHexWeighted Graphplay.SimpleGraph.toWeighted at hxy ⊢
    by_cases h : (HeavyHexLattice 33 34).Adj x y
    · simp [_root_.SimpleGraph.adjMatrix_apply, h]
    · simp [_root_.SimpleGraph.adjMatrix_apply, h] at hxy
  simp only [hval, heronAllowedPhases, Set.mem_setOf_eq, norm_one]

/-- **Quotient satisfaction.**  The data/flag quotient of any heavy-hex
chip satisfies the *relaxed* spec `ibmHeronSpec.quotient`, by
`WeightedGraph.satisfies_quotient`.  Concretely, this says the 2 x 2
quotient walk is implementable on the same hardware (it sits on the
chip's tunable-coupler frame). -/
theorem heavyHex_quotient_satisfies (n m : ℕ)
    (embed : HeavyHexVertex n m → ℝ × ℝ)
    (hG : (heavyHexWeighted n m).satisfies ibmHeronSpec embed)
    -- the two genuine hypotheses the migrated `satisfies_quotient` now requires:
    -- every role-cell is realised by a qubit (no empty-cell qubit-count blow-up),
    -- and the real-rescaled quotient couplings stay inside the hardware phase set.
    (hsurj : Function.Surjective (dataFlagPartition n m).cells)
    (hphase : ∀ i j : Role,
      ((dataFlagPartition n m).quotientHWGraph).adj i j ≠ 0 →
        ((dataFlagPartition n m).quotientHWGraph).adj i j ∈ ibmHeronSpec.allowedPhaseSet) :
    -- The data/flag quotient graph satisfies the relaxed (quotient) spec under
    -- some induced (centroid) embedding of the two role-cells.
    ∃ embed_quotient : Role → ℝ × ℝ,
      ((dataFlagPartition n m).quotientHWGraph).satisfies
        ibmHeronSpec.quotient embed_quotient :=
  WeightedGraph.satisfies_quotient hG (dataFlagPartition n m) hsurj hphase

/-! ## 7. Three concrete engineering payoffs.

Each of the following is stated as a `theorem` with `sorry`.  They are the
three "things you can actually build on Heron / Eagle" extracted by the
spectral disassembly above. -/

/-! ### Payoff #1: PST between two specified data qubits.

PST on the chip between two specific data qubits `u` and `v` is *not*
automatic from cell-uniform PST.  But on a heavy-hex chip whose row and
column symmetries align the two qubits within the data cell, the
*cell-uniform* PST result lifts to two-qubit PST under an additional
symmetry hypothesis — namely that the chip has an automorphism
exchanging `u` and `v`, which holds for the chip's centre-of-mass-symmetric
pairs.

The protocol: prepare the equal-superposition state over `{u, v}`, evolve
for time `π / (2q)` (`q = 2√(N−1) = dataFlagCoupling n m`), the cell-uniform
component swaps to flag-uniform; then re-evolve for another `π / (2q)` (or
equivalently use the involution property of the `K_2` walk) to land back on
`{u, v}` with the amplitudes swapped — total transfer time `π / q`. -/

/-- **Payoff #1.**  Let `u, v : HeavyHexVertex n m` be two data qubits
related by a chip automorphism `α : HeavyHexLattice n m → HeavyHexLattice n m`
with `α u = v`.  Then there is a CTQW protocol on the IBM-Heron-native
couplings that takes `|u⟩` to a state with `|⟨v|·⟩| = 1` at the genuine
two-qubit transfer time `t = π / q`, where `q = dataFlagCoupling n m = 2√(N−1)`
(twice the quotient PST time `π/(2q)`).

FALSE→TRUE MIGRATION (transfer-time constant fix).  The prior statement pinned
the time to `t = π / √6`.  Here `√6 = √(3·2)` is the *honeycomb-template*
interior coupling (degree-3 data row times degree-2 flag row); it is **not** the
coupling of the concrete `HeavyHexLattice n m`, whose data row-sum is the
complete-site dart count `2(N−1)`, giving `q = 2√(N−1)` (see
`dataFlagQuotient_toroidal_form` / `dataFlag_symmQuotient_form`).  The two never
agree: `2√(N−1) = √6 ⇔ 4(N−1) = 6 ⇔ N = 5/2`, impossible for a vertex count `N`.
So `π/√6` is the wrong transfer time for this lattice and the old existential was
false as stated; we replace it with the genuine `π / dataFlagCoupling n m` and
require `0 < n, 0 < m` so the coupling is positive (`dataFlagCoupling_pos`).

HONEST `sorry` on a TRUE statement.  Reducing the cell-uniform PST lift
(`heavyHex_pst_lift`, fully proved) to *single-qubit* PST `‖evolve τ u v‖ = 1`
is the Bachman–Tamon automorphism-averaging argument (arXiv:1108.0339): the
swap automorphism `α` makes `span{|u⟩,|v⟩}` an invariant `K_2`-subspace of the
walk, on which the evolution is the `2×2` quotient walk.  That invariant-subspace
machinery is not developed in this scaffold, so this carries an honest `sorry` on
the (now correctly-timed) TRUE statement. -/
theorem ibm_native_pst_two_qubit (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (u v : HeavyHexVertex n m) (hu : role u = Role.data)
    (hv : role v = Role.data)
    (hAut : ∃ α : (HeavyHexLattice n m) →g (HeavyHexLattice n m),
              α.toFun u = v ∧ α.toFun v = u) :
    ∃ τ : ℝ, τ = Real.pi / dataFlagCoupling n m ∧
      IsPST (heavyHexWeighted n m) u v τ := by
  -- Combine the cell-uniform PST lift (`heavyHex_pst_lift`) with the
  -- chip-automorphism averaging, an instance of the Bachman–Tamon
  -- automorphism trick: `span{u,v}` is an invariant `K_2`-subspace.
  refine ⟨Real.pi / dataFlagCoupling n m, rfl, ?_⟩
  -- HONEST sorry: needs Bachman–Tamon automorphism-averaging
  -- (cell-uniform PST → single-qubit PST via the invariant 2-dim subspace).
  sorry

/-! ### Payoff #2: Noise-symmetric subspace identification.

A noise model `N` *preserves* the data/flag partition iff each of its
Lindblad operators is cell-uniform-preserving.  Practical heavy-hex noise
sources:

* **Per-vertex dephasing** with *uniform* rate is automatically cell-uniform-
  symmetric (every projector `|x⟩⟨x|` preserves cell membership).
* **Per-vertex amplitude damping** with *uniform* rate, ditto.
* **Per-edge cross-talk** with rate depending only on (role, role) is
  cell-uniform-symmetric — but non-uniform per-edge cross-talk in general is
  not. -/

/-- **Payoff #2.**  Uniform-rate dephasing noise on the heavy-hex chip is
cell-uniform-symmetric with respect to the data/flag partition — **provided
every cell is a singleton**.

CORRECTNESS FIX: with the bare-`mulVec` `Matrix.preservesCellUniform` of
`Toolkit/Noise.lean`, the unconditional statement is *false* whenever a cell
has size `> 1` — the single-site projector `|v⟩⟨v|` sends the cell-uniform
all-ones state to a vector supported on `{v}` alone (exactly the obstruction
proved in `perEdge_crossTalk_may_break_dataFlag`).  The genuinely-true
bare-vector statement requires the partition to be discrete (`hsingle`: each
role class is a singleton), under which every vector is trivially cell-uniform
and every operator is cell-uniform-preserving.  (The unconditional physical
content — that parity-respecting dephasing commutes with the cell-average
superoperator — is a *density-matrix / Lindblad-superoperator* statement, not
expressible with this vector-level predicate.) -/
theorem dephasing_preserves_dataFlag (n m : ℕ) (rate : ℝ)
    (hsingle : ∀ x y : HeavyHexVertex n m,
        (dataFlagPartition n m).cells x = (dataFlagPartition n m).cells y → x = y) :
    (NoiseModel.dephasingNoise (HeavyHexVertex n m) rate).cellUniformSymmetric
      (dataFlagPartition n m) := by
  intro L _ ψ _ x y hxy
  -- `hsingle` collapses the cell relation to equality, so `x = y`.
  rw [hsingle x y hxy]

/-- Companion: uniform-rate amplitude damping also preserves the partition,
under the same discrete-cells hypothesis.

CORRECTNESS FIX (same as `dephasing_preserves_dataFlag`): the matrix-unit jump
operators are not cell-uniform-preserving at the bare-vector level for cells of
size `> 1`; the unconditional statement is false (cf.
`perEdge_crossTalk_may_break_dataFlag`).  We add the genuinely-needed
discrete-cells hypothesis `hsingle`.  The unconditional truth lives at the
Lindblad-superoperator level. -/
theorem amplitudeDamping_preserves_dataFlag (n m : ℕ) (rate : ℝ)
    (hsingle : ∀ x y : HeavyHexVertex n m,
        (dataFlagPartition n m).cells x = (dataFlagPartition n m).cells y → x = y) :
    (NoiseModel.amplitudeDamping (HeavyHexVertex n m) rate).cellUniformSymmetric
      (dataFlagPartition n m) := by
  intro L _ ψ _ x y hxy
  rw [hsingle x y hxy]

/-- A *non*-example: arbitrary per-edge cross-talk does *not* preserve the
partition.  Genuine statement: for a heavy-hex chip large enough to have a data
cell of size `> 1` (e.g. `n = m = 2`), there is a `NoiseModel` that is **not**
cell-uniform-symmetric for the data/flag partition. -/
theorem perEdge_crossTalk_may_break_dataFlag :
    ∃ N : NoiseModel (HeavyHexVertex 2 2),
      ¬ N.cellUniformSymmetric (dataFlagPartition 2 2) := by
  classical
  -- Two distinct data qubits in the (large) data cell of the 2×2 chip.
  set x : HeavyHexVertex 2 2 := .data (⟨0, by norm_num⟩, ⟨0, by norm_num⟩, false) with hx
  set x' : HeavyHexVertex 2 2 := .data (⟨0, by norm_num⟩, ⟨0, by norm_num⟩, true) with hx'
  -- Witness noise: a single jump operator `|x⟩⟨x|` supported on `x` alone.
  refine ⟨{ lindblad_operators := {Matrix.single x x 1}, coherence_rates := fun _ => 0 }, ?_⟩
  intro hsym
  -- `single x x 1 ∈ lindblad_operators` preserves cell-uniformity by hypothesis.
  have hL : Matrix.single x x 1 ∈
      ({ lindblad_operators := {Matrix.single x x 1},
          coherence_rates := fun _ => 0 } : NoiseModel (HeavyHexVertex 2 2)).lindblad_operators :=
    Finset.mem_singleton_self _
  have hpres := hsym (Matrix.single x x 1) hL
  -- Apply to the all-ones (cell-uniform) state.
  have hconst : ∀ a b : HeavyHexVertex 2 2,
      (dataFlagPartition 2 2).cells a = (dataFlagPartition 2 2).cells b →
      (fun _ => (1 : ℂ)) a = (fun _ => (1 : ℂ)) b := fun _ _ _ => rfl
  -- `x` and `x'` are in the same (data) cell.
  have hcell : (dataFlagPartition 2 2).cells x = (dataFlagPartition 2 2).cells x' := rfl
  have hxx' : x ≠ x' := by rw [hx, hx']; decide
  have hkey := hpres (fun _ => 1) hconst x x' hcell
  -- `(single x x 1).mulVec (const 1)` is `1` at `x`, `0` at `x'`: contradiction.
  rw [Matrix.single_mulVec] at hkey
  rw [Function.update_self, Function.update_of_ne (Ne.symm hxx')] at hkey
  simp only [mul_one, Pi.zero_apply] at hkey
  exact one_ne_zero hkey

/-! ### Payoff #3: Chiral-signing optimisation for fast mixing.

This is the heavy-hex analogue of the K_4 chiral signing of Levine et al.
(arXiv:2605.04414).  On the 2 x 2 data/flag quotient, the only nontrivial
unitary signing is `Q' = [[0, q·e^{iφ}], [q·e^{-iφ}, 0]]` for some real
phase `φ`, with the *realized* coupling `q = dataFlagCoupling n m = 2√(N−1)`
(the `K_N`-subdivision value — **not** the honeycomb-template `√6`; see the file
header).  Its mixing time depends on the **magnitude** of the spectral
gap, which is `‖e^{iφ} · q‖ = q` — invariant under `φ`!

This means: chiral signings of the 2 x 2 quotient achieve no mixing-time
speedup over the unsigned walk.  This is a *negative* result and is itself
informative: the heavy-hex's *2-cell* quotient is too coarse to exhibit
chiral speedup; a finer (3- or 4-cell) refinement is required.

The positive statement: on a 3-cell refined quotient where data-3-degree,
data-2-degree, and flag are separate cells, chiral signings *do* open a
spectral gap.  Optimising over the unitary signings of that quotient gives
the optimal cell-uniform mixing time, by `chiral_mixing_optimization`. -/

/-- **Payoff #3 (negative half).**  On the *2-cell* data/flag quotient,
chiral signings do not change the mixing time, because the chiral phase leaves
the eigenvalue *moduli* of the (Hermitian) 2×2 quotient unchanged.  Genuine
statement: for any unit-modulus, Hermitian, diagonal-`1` quotient phasing `τ`,
the off-diagonal magnitudes of the signed symmetric quotient coincide with
those of the unsigned one, so its two eigenvalues are `±|q|` exactly as in the
unsigned case (the spectral gap, hence the mixing time, is `τ`-independent). -/
theorem dataFlag_chiral_no_speedup (n m : ℕ) :
    ∀ (τ : Role → Role → ℂ),
      (∀ r s, ‖τ r s‖ = 1) → (∀ r s, τ s r = star (τ r s)) →
      (∀ r, τ r r = 1) →
      -- the off-diagonal magnitude of the signed quotient `‖τ·q‖` equals the
      -- unsigned magnitude `‖q‖`, for every off-diagonal pair `(r, s)`.
      ∀ r s : Role, r ≠ s →
        ‖τ r s * (dataFlagPartition n m).symmQuotient r s‖
          = ‖(dataFlagPartition n m).symmQuotient r s‖ := by
  intro τ hτ _ _ r s _
  rw [norm_mul, hτ r s, one_mul]

/-- **Spectrum of any zero-diagonal Hermitian `2×2` `Role`-matrix.**  If `M` has
vanishing diagonal and Hermitian off-diagonal entries `M data flag = a`,
`M flag data = star a` of modulus `‖a‖ = r`, then `det(lam·I − M) = lam² − r²`
(`star a · a = ‖a‖² = r²`), so the spectrum is exactly `{r, −r}` — depending on
`a` *only through its modulus* `r`.  This is the matrix-level engine of Payoff #3:
a chiral phase `a = r·e^{iφ}` leaves the spectrum (hence the spectral radius `r`
and the mixing time) **completely** unchanged. -/
theorem roleHermitian_spectrum (a : ℂ) (r : ℝ) (hr : ‖a‖ = r) (lam : ℂ)
    (M : Matrix Role Role ℂ)
    (hDD : M Role.data Role.data = 0) (hFF : M Role.flag Role.flag = 0)
    (hDF : M Role.data Role.flag = a) (hFD : M Role.flag Role.data = star a) :
    lam ∈ spectrum ℂ M ↔ lam = (r : ℂ) ∨ lam = -(r : ℂ) := by
  classical
  -- `star a · a = ‖a‖² = r²`.
  have hstar : star a * a = ((r : ℂ)) ^ 2 := by
    rw [Complex.star_def, RCLike.conj_mul, ← hr]
    norm_cast
  -- spectrum ↔ det = 0.
  let e : Role ≃ Fin 2 :=
    { toFun := fun ro => match ro with | Role.data => 0 | Role.flag => 1
      invFun := fun i => if i = 0 then Role.data else Role.flag
      left_inv := by intro ro; cases ro <;> rfl
      right_inv := by intro i; fin_cases i <;> rfl }
  rw [spectrum.mem_iff, Matrix.algebraMap_eq_diagonal, Matrix.isUnit_iff_isUnit_det,
      isUnit_iff_ne_zero, not_not]
  rw [show ((algebraMap ℂ (Role → ℂ)) lam) = (fun _ : Role => lam) from by
        funext ro; simp [Algebra.algebraMap_eq_smul_one]]
  have hdet : (Matrix.diagonal (fun _ : Role => lam) - M).det = lam ^ 2 - (r : ℂ) ^ 2 := by
    rw [← Matrix.det_reindex_self e, Matrix.det_fin_two]
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sub_apply,
      Matrix.diagonal_apply]
    have h00 : (e.symm 0) = Role.data := rfl
    have h11 : (e.symm 1) = Role.flag := rfl
    rw [h00, h11, hDD, hFF, hDF, hFD]
    simp only [if_true, if_neg (by decide : ¬ (Role.data = Role.flag)),
        if_neg (by decide : ¬ (Role.flag = Role.data))]
    rw [show (lam - 0) * (lam - 0) - (0 - a) * (0 - star a)
          = lam ^ 2 - star a * a by ring, hstar]
  rw [hdet, sub_eq_zero, sq_eq_sq_iff_eq_or_eq_neg]

/-- **Payoff #3 (negative half, spectral form).**  The chiral-signed symmetric
data/flag quotient `M' = [[0, e^{iφ}·q], [e^{−iφ}·q, 0]]` (any unit-modulus
Hermitian diagonal-`1` phasing `τ`) has the **same** spectrum `{±q}`,
`q = 2√(N−1)`, as the unsigned quotient — *independent of the phase* `φ`.  Hence
the spectral radius is `q` for every chiral signing: no mixing-time speedup is
available on the 2-cell quotient. -/
theorem dataFlag_chiral_spectrum_phase_independent (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (τ : Role → Role → ℂ) (hτ : ∀ r s, ‖τ r s‖ = 1)
    (hτh : ∀ r s, τ s r = star (τ r s)) (lam : ℂ) :
    lam ∈ spectrum ℂ
        (Matrix.of fun r s => τ r s * (dataFlagPartition n m).symmQuotient r s) ↔
      lam = (dataFlagCoupling n m : ℂ) ∨ lam = -(dataFlagCoupling n m : ℂ) := by
  classical
  set M : Matrix Role Role ℂ :=
    Matrix.of fun r s => τ r s * (dataFlagPartition n m).symmQuotient r s with hM
  obtain ⟨hfd, hdd, hff⟩ := dataFlag_symmQuotient_form n m hn hm
  have hdf := symmQuotient_dataFlag n m hn hm
  -- The signed off-diagonal entry and its modulus.
  set q : ℝ := dataFlagCoupling n m with hq
  have hqval : q = 2 * Real.sqrt ((Fintype.card (HoneyVertex n m) : ℝ) - 1) := rfl
  have hqpos : 0 ≤ q := (dataFlagCoupling_pos n m hn hm).le
  -- off-diagonal entry `a = τ(data,flag)·q`, modulus `q`.
  have hdfc : (dataFlagPartition n m).symmQuotient Role.data Role.flag = (q : ℂ) := by
    rw [hdf]; rw [hqval]
  have hMDF : M Role.data Role.flag = τ Role.data Role.flag * (q : ℂ) := by
    rw [hM]; simp only [Matrix.of_apply]; rw [hdfc]
  have hqc : (dataFlagPartition n m).symmQuotient Role.flag Role.data = (q : ℂ) := by
    rw [hfd]; rw [hqval]
  have hMFD : M Role.flag Role.data = star (τ Role.data Role.flag * (q : ℂ)) := by
    rw [hM]; simp only [Matrix.of_apply]
    rw [hqc, hτh Role.data Role.flag]
    rw [star_mul', Complex.star_def, Complex.conj_ofReal]
  have hMDD : M Role.data Role.data = 0 := by
    rw [hM]; simp only [Matrix.of_apply, hdd, mul_zero]
  have hMFF : M Role.flag Role.flag = 0 := by
    rw [hM]; simp only [Matrix.of_apply, hff, mul_zero]
  have hnorm : ‖τ Role.data Role.flag * (q : ℂ)‖ = q := by
    rw [norm_mul, hτ Role.data Role.flag, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hqpos]
  rw [roleHermitian_spectrum (τ Role.data Role.flag * (q : ℂ)) q hnorm lam M
      hMDD hMFF hMDF hMFD]

/-- **Payoff #3 (positive half).**  On a 3-cell refinement of the
data/flag partition (separating data-degree-3 from data-degree-2 boundary
qubits), the optimal chiral signing of the quotient achieves a cell-uniform
mixing speedup on the chip *at a specific resonance time*.

Existence statement: there is a refined index type `I`, an equitable
partition `P` of the chip into `I` cells, a chiral signing `s` cross-
constant on those cells, AND a single resonance time `t > 0` at which the
resulting signed bundle is cell-uniformly mixing.

CORRECTNESS FIX (replaces a *false* prior statement): the previous version
quantified `∀ t`, asserting cell-uniform mixing at *every* time — false in
general, since uniform mixing is a *resonance* phenomenon that holds only at
isolated times (cf. the `1/√2` mixing time `π/(4q)` of the 2-cell quotient,
which is NOT mixing at other `t`).  The honest shape is the existential
`∃ t > 0` over the resonance time.

⚠ CONDITIONAL / `sorry`-DEPENDENT.  This carries an honest `sorry`: it needs
the 3-cell boundary refinement (`{data-3, data-2, flag}`, equitable on the open
lattice — see Open Question 3 below) together with the upstream
`CellUniformMixing` resonance-time machinery, neither of which is developed in
this scaffold.  It is NOT a clean `#print axioms`-verified result. -/
theorem refined_chiral_speedup (n m : ℕ) :
    ∃ (I : Type) (_ : Fintype I) (_ : DecidableEq I)
      (P : EquitablePartition (heavyHexWeighted n m) I)
      (s : ChiralSigning (HeavyHexVertex n m))
      (h : s.CrossConstant P.cells)
      (t : ℝ), 0 < t ∧
        ((⟨heavyHexWeighted n m, P⟩ :
          Bundle (HeavyHexVertex n m) I).signedBy s h).CellUniformMixing t := by
  -- BLOCKED: needs the 3-cell boundary refinement + upstream resonance-time
  -- CellUniformMixing machinery (honest sorry; conditional result).
  sorry

/-! ## Open questions / future work for this application.

1.  **Exact embedding match.**  The `(n, m) = (7, 18)` rectangle for Eagle
    is an upper-bound rectangle; IBM Eagle has an *irregular* truncation
    that reduces the count to exactly 127.  A faithful embedding would
    encode the truncation as a vertex-subset hypothesis.

2.  **Tunable-coupler phase set.**  We took `heronAllowedPhases = unit
    circle`; the actual set is a fine but discrete subset determined by
    the control hardware's clock resolution.  Matching the real set is
    a hardware-spec engineering question.

3.  **Boundary refinement.**  The 2-cell data/flag partition is only
    equitable on the toroidal heavy-hex.  The 3-cell `{data-3, data-2,
    flag}` refinement is equitable on the open lattice; a 4-cell variant
    that further separates corner data qubits is equitable on rectangular
    boundaries.  Working these out is a worked example for
    `EquitablePartition.refine`.

4.  **Surface-code interplay.**  Heavy-hex was designed to be compatible
    with subsystem surface codes (Chamberland et al. 1907.09528).  The
    data/flag partition coincides with the role split in those codes,
    suggesting that the equitable-partition lift gives a natural way to
    talk about logical operators as cell-uniform observables.  Worth
    spelling out.

5.  **Chiral hyper-cube / honeycomb signings.**  An analogue of the
    Levine et al. K_4 chiral signing for the *honeycomb* (rather than
    K_4) quotient would give an optimal chiral CTQW recipe for heavy-hex.
    The signing exists by the Levine construction applied to K_3 (the
    honeycomb's chromatic core), but its explicit phases on the heavy-hex
    haven't been worked out. -/

end IBMHeavyHex
end Applications
end Graphplay
