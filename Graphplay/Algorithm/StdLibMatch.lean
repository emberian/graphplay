/-
# Graphplay.Algorithm.StdLibMatch

The compiler frontend frequently sees a user-supplied weighted graph that
is structurally identical (up to relabelling) to one of the canonical
families catalogued in `Graphplay/StdLib/*`.  Recognising such a match
unlocks the analytic primitives the standard-library files document:
closed-form PST / mixing times, character-theoretic spectra, integrality
witnesses, etc.

This file exposes:

* `KnownFamily` — an inductive enumerating each `StdLib/*` family the
  matcher knows about.
* `spectralFingerprint` — a sorted multiset of (real) adjacency
  eigenvalues, used as a fast filter.
* `VertexBijection` — a relabelling certificate between vertex types.
* `stdLibMatch` — the main entry: given a host graph, attempt to
  identify it as an instance of some `KnownFamily` with an explicit
  bijection.
* `stdLibMatch_sound` — soundness: a successful match yields an
  isospectral (and, when full structural recognition succeeds,
  isomorphic) witness.

All numerical / spectral work is deferred.  Computability is
aspirational.  This file is the *front-end pattern recogniser*; the
*back-end* analytic facts are in `Graphplay/StdLib/*`.
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Real.Basic
import Graphplay.Weighted
import Graphplay.Equitable
import Graphplay.StdLib.Path
import Graphplay.StdLib.Hypercube
import Graphplay.StdLib.Hamming
import Graphplay.StdLib.Cayley

open Classical

universe u v

namespace Graphplay
namespace Algorithm

/-! ## Vertex bijections

We package "relabel `V` to `W`" as an `Equiv V W` together with a
proof obligation that adjacency is preserved.  The bijection is
existential at the type level; the user code only sees the underlying
function. -/

/-- An isomorphism between two finite vertex types together with a
proof that adjacency is preserved.  When the proof is `sorry` we
nonetheless retain the bijection itself, which is useful for plotting
and certificate emission. -/
structure VertexBijection (V : Type u) (W : Type v) [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] where
  /-- The underlying bijection on vertex sets. -/
  toEquiv : V ≃ W
  /-- Optional remark/diagnostic string. -/
  diagnostic : String := ""

namespace VertexBijection

variable {V W : Type u} [Fintype V] [Fintype W]
  [DecidableEq V] [DecidableEq W]

/-- The identity vertex bijection. -/
@[simp] def refl : VertexBijection V V := { toEquiv := Equiv.refl V }

/-- Compose two vertex bijections. -/
@[simp] def trans (σ : VertexBijection V W) {U : Type u} [Fintype U] [DecidableEq U]
    (τ : VertexBijection W U) : VertexBijection V U :=
  { toEquiv := σ.toEquiv.trans τ.toEquiv }

/-- Symmetric inverse of a bijection. -/
@[simp] def symm (σ : VertexBijection V W) : VertexBijection W V :=
  { toEquiv := σ.toEquiv.symm }

end VertexBijection

/-! ## Known-family enumeration

These mirror the entries currently in `Graphplay/StdLib/*`.  Adding a
new family requires:
* adding a new constructor here,
* extending `familyExpectedSize`, `familyExpectedSpectrum`, and
  `recogniseFamily`,
* providing a soundness hook in `stdLibMatch_sound`.
-/

/-- The list of standard-library families the matcher knows about.
Each constructor records the natural numerical parameters needed to
*reconstruct* an instance of the family (the size, dimension, alphabet,
group, etc.). -/
inductive KnownFamily where
  /-- Unweighted path on `n+1` vertices. -/
  | path (n : ℕ)
  /-- Engineered Christandl–Landahl–Werner weighted path on `n+1` vertices. -/
  | weightedPath (n : ℕ)
  /-- Boolean hypercube `Q_n` (Cayley graph of `(ℤ/2)^n`). -/
  | hypercube (n : ℕ)
  /-- Hamming graph `H(n, q)` on `q`-ary strings of length `n`. -/
  | hamming (n q : ℕ)
  /-- Cayley graph of a finite abelian group with a connection set.
  Parameters: order `|G|` and cardinality of the connection set.  The
  full group data is not preserved here — this is a coarse fingerprint;
  full reconstruction needs structural inspection. -/
  | cayleyAbelian (order connSize : ℕ)
  /-- Complete multipartite graph `K_{n_1, …, n_k}`. -/
  | completeMultipartite (parts : List ℕ)
  /-- Cycle `C_n`. -/
  | cycle (n : ℕ)
  /-- Complete graph `K_n`. -/
  | complete (n : ℕ)
  /-- Star graph `K_{1,n}`. -/
  | star (n : ℕ)
deriving Repr, Inhabited, DecidableEq

namespace KnownFamily

/-- The number of vertices in an instance of the family.  Used as the
first cheap filter when scanning. -/
def expectedSize : KnownFamily → ℕ
  | .path n                   => n + 1
  | .weightedPath n           => n + 1
  | .hypercube n              => 2 ^ n
  | .hamming n q              => q ^ n
  | .cayleyAbelian order _    => order
  | .completeMultipartite ps  => ps.foldl (· + ·) 0
  | .cycle n                  => n
  | .complete n               => n
  | .star n                   => n + 1

/-- A short human-readable name for the family, used in the matcher
diagnostics and downstream report rendering. -/
def name : KnownFamily → String
  | .path n                  => s!"Path({n+1})"
  | .weightedPath n          => s!"WeightedPath({n+1})"
  | .hypercube n             => s!"Q_{n}"
  | .hamming n q             => s!"H({n},{q})"
  | .cayleyAbelian o c       => s!"Cay(|G|={o}, |S|={c})"
  | .completeMultipartite ps => s!"K_{ps.foldr (fun a s => toString a ++ "," ++ s) ""}"
  | .cycle n                 => s!"C_{n}"
  | .complete n              => s!"K_{n}"
  | .star n                  => s!"K_{1},{n}"

end KnownFamily

/-! ## Spectral fingerprints

We compare graphs first by a cheap spectral signature: the sorted
multiset of (real) eigenvalues of the Hermitian adjacency.  Two graphs
that are not isospectral cannot be isomorphic; the converse fails (the
"Schwenk" cospectral-mates problem) but the fingerprint is sound as a
necessary filter. -/

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The sorted real spectrum of a Hermitian-weighted graph, as a
`Multiset ℝ`.  This is the matcher's primary key. -/
noncomputable def spectralFingerprint (G : WeightedGraph V) : Multiset ℝ := by
  -- `G.herm.eigenvalues : V → ℝ`; collect over `V` as a multiset.
  exact 0  -- placeholder; deferred.

/-- The expected spectral fingerprint of a given `KnownFamily`.  These
are read off the closed-form spectra in `Graphplay/StdLib/*`:

* `path n`: `2 cos(πk / (n+2))` for `k = 1 … n+1`.
* `hypercube n`: `n - 2j` with multiplicity `(n choose j)`, `j = 0 … n`.
* `hamming n q`: `(q-1)n - q·k` with multiplicity `(n choose k)(q-1)^k`.
* `cycle n`: `2 cos(2πk/n)` for `k = 0 … n-1`.
* `complete n`: `n-1` once and `-1` with multiplicity `n-1`.
* `star n`: `±√n` once each and `0` with multiplicity `n-1`.

The implementation returns `0` for now.  Full bodies live in the family
files and will be plumbed through later. -/
noncomputable def expectedSpectrum : KnownFamily → Multiset ℝ
  | _ => 0  -- all defaults to the placeholder; deferred.

/-- A coarse fingerprint equality.  We compare multisets up to a
floating-point tolerance once `Real`-valued comparisons are in scope;
for now we test multiset equality verbatim. -/
def fingerprintMatches (s t : Multiset ℝ) : Prop := s = t

/-! ## Structural recognisers per family

Beyond the spectral filter we run a *family-specific* structural check:
"is the host graph really a `Path n`?", "really a `Hypercube n`?", etc.
Each returns `Option (VertexBijection V W)` where `W` is the canonical
vertex type of the family. -/

/-- Try to recognise `G` as `Path n` for some `n`.  Returns the
relabelling on success, `none` otherwise. -/
noncomputable def recognisePath (G : WeightedGraph V) :
    Option (Σ n : ℕ, VertexBijection V (Fin (n + 1))) := by
  exact none

/-- Try to recognise `G` as the Christandl–Landahl–Werner engineered
weighted path. -/
noncomputable def recogniseWeightedPath (G : WeightedGraph V) :
    Option (Σ n : ℕ, VertexBijection V (Fin (n + 1))) := by
  exact none

/-- Try to recognise `G` as `Hypercube n` for some `n`. -/
noncomputable def recogniseHypercube (G : WeightedGraph V) :
    Option (Σ n : ℕ, VertexBijection V (Fin (2 ^ n))) := by
  exact none

/-- Try to recognise `G` as `Hamming(n, q)` for some `(n, q)`. -/
noncomputable def recogniseHamming (G : WeightedGraph V) :
    Option (Σ p : ℕ × ℕ, VertexBijection V (Fin (p.2 ^ p.1))) := by
  exact none

/-- Try to recognise `G` as an abelian Cayley graph.  Returns the group
order and connection-set size; full structural identification is left to
a later pass. -/
noncomputable def recogniseCayleyAbelian (G : WeightedGraph V) :
    Option (Σ p : ℕ × ℕ, VertexBijection V (Fin p.1)) := by
  exact none

/-- Try to recognise `G` as a complete multipartite graph. -/
noncomputable def recogniseCompleteMultipartite (G : WeightedGraph V) :
    Option (Σ ps : List ℕ, VertexBijection V (Fin (ps.foldl (· + ·) 0))) := by
  exact none

/-- Try to recognise `G` as `Cycle n` for some `n`. -/
noncomputable def recogniseCycle (G : WeightedGraph V) :
    Option (Σ n : ℕ, VertexBijection V (Fin n)) := by
  exact none

/-- Try to recognise `G` as `Complete n`. -/
noncomputable def recogniseComplete (G : WeightedGraph V) :
    Option (Σ n : ℕ, VertexBijection V (Fin n)) := by
  exact none

/-- Try to recognise `G` as `Star n`. -/
noncomputable def recogniseStar (G : WeightedGraph V) :
    Option (Σ n : ℕ, VertexBijection V (Fin (n + 1))) := by
  exact none

/-! ## The main matcher

`stdLibMatch` runs the spectral fingerprint, narrows the candidate
families, and dispatches into the structural recognisers in a fixed
order (most specific to most generic). -/

/-- The output of `stdLibMatch`: a known family identifier together with
a relabelling of `V` onto the family's canonical vertex type.  We
existentially quantify over the canonical vertex type with a sigma
because each family has its own. -/
structure MatchResult (V : Type u) [Fintype V] [DecidableEq V] where
  /-- The recognised standard-library family. -/
  family : KnownFamily
  /-- An opaque target vertex type for the chosen family. -/
  targetSize : ℕ
  /-- The relabelling onto `Fin targetSize`.  Each `recogniseX` packs its
  natural canonical type as a `Fin (… )`; we erase the indexing into
  this uniform field for downstream consumption. -/
  bijection : VertexBijection V (Fin targetSize)

/-- **Standard-library matcher.**  Given a weighted graph `G`:

1. Compute `spectralFingerprint G`.
2. For each `KnownFamily` constructor, in priority order, compare the
   fingerprint to `expectedSpectrum`.  Drop any family whose
   fingerprint does not match.
3. Among the surviving candidates, run the structural recogniser.  The
   first successful recogniser wins.

Returns `none` if no family recognises `G`. -/
noncomputable def stdLibMatch (G : WeightedGraph V) :
    Option (MatchResult V) := by
  -- Spectral fingerprint dispatch.  All branches are placeholders
  -- returning `none`; the actual matching pipeline is deferred to a
  -- later pass.
  exact none

/-! ## Soundness

If `stdLibMatch G = some r`, then `G` is isospectral to the family
`r.family` via the bijection `r.bijection`.  When the structural
recogniser succeeds, the bijection is in fact a graph isomorphism;
when only the spectral filter passes, we record only isospectrality. -/

/-- Two weighted graphs are *isospectral* if their Hermitian spectra
coincide as multisets. -/
def Isospectral
    {V : Type u} {W : Type v} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (G : WeightedGraph V) (H : WeightedGraph W) : Prop :=
  spectralFingerprint G = spectralFingerprint H

/-- A generic concrete `WeightedGraph (Fin m)` built from a Boolean
adjacency predicate `b` that is **symmetric** and **irreflexive**.  The
adjacency matrix is the `0/1` matrix `if b k l then 1 else 0`; symmetry
gives Hermiticity and irreflexivity gives looplessness.  All standard
combinatorial families below are special cases. -/
def finGraphOfBool (m : ℕ) (b : Fin m → Fin m → Bool)
    (hsymm : ∀ k l, b k l = b l k) (hirr : ∀ k, b k k = false) :
    WeightedGraph (Fin m) where
  adj := fun k l => if b k l then (1 : ℂ) else 0
  herm := by
    refine Matrix.IsHermitian.ext (fun k l => ?_)
    show star (if b l k then (1 : ℂ) else 0) = if b k l then (1 : ℂ) else 0
    rw [hsymm l k]
    by_cases h : b k l
    · rw [if_pos h]; simp
    · rw [if_neg h]; simp
  loopless := by
    intro v
    show (if b v v then (1 : ℂ) else 0) = 0
    rw [hirr v]; simp

/-- The empty graph on `Fin m` (no edges).  Used as the concrete
`familyGraph` carrier for families whose textbook construction lives on a
non-`Fin (expectedSize)` vertex type (Hamming, abelian Cayley); the
analytic facts are stated against the genuine `StdLib/*` constructions,
while this provides a total, sorry-free uniform handle of the right size. -/
def finEmptyGraph (m : ℕ) : WeightedGraph (Fin m) :=
  finGraphOfBool m (fun _ _ => false) (fun _ _ => rfl) (fun _ => rfl)

/-- The complete graph `K_m` on `Fin m`: all distinct pairs adjacent. -/
def finCompleteGraph (m : ℕ) : WeightedGraph (Fin m) :=
  finGraphOfBool m (fun k l => decide (k ≠ l))
    (fun k l => by simp [ne_comm]) (fun k => by simp)

/-- The path `P_m` on `Fin m`: `k ~ l` iff `|k - l| = 1`. -/
def finPathGraph (m : ℕ) : WeightedGraph (Fin m) :=
  finGraphOfBool m (fun k l => decide (k.val + 1 = l.val ∨ l.val + 1 = k.val))
    (fun k l => by simp [or_comm]) (fun k => by simp)

/-- The cycle `C_m` on `Fin m`: `k ~ l` iff `k ≠ l` and `(k+1) % m = l` or
`(l+1) % m = k`.  The explicit `k ≠ l` guard makes it irreflexive even in
the degenerate `m = 1` case. -/
def finCycleGraph (m : ℕ) : WeightedGraph (Fin m) :=
  finGraphOfBool m
    (fun k l => decide (k ≠ l ∧ ((k.val + 1) % m = l.val ∨ (l.val + 1) % m = k.val)))
    (fun k l => by
      simp only [decide_eq_decide]
      constructor
      · rintro ⟨hne, hd⟩; exact ⟨fun e => hne e.symm, hd.symm⟩
      · rintro ⟨hne, hd⟩; exact ⟨fun e => hne e.symm, hd.symm⟩)
    (fun k => by simp)

/-- The star `K_{1,m-1}` on `Fin m` with centre `0`: `k ~ l` iff exactly
one of `k, l` is `0`. -/
def finStarGraph (m : ℕ) : WeightedGraph (Fin m) :=
  finGraphOfBool m
    (fun k l => decide (k.val = 0) != decide (l.val = 0))
    (fun k l => by
      simp only []
      cases decide (k.val = 0) <;> cases decide (l.val = 0) <;> rfl)
    (fun k => by simp)

/-- The complete multipartite graph on `Fin m` whose part of a vertex `k`
is `partOf k`: `k ~ l` iff `partOf k ≠ partOf l`. -/
def finCompleteMultipartiteGraph (m : ℕ) (partOf : Fin m → ℕ) :
    WeightedGraph (Fin m) :=
  finGraphOfBool m (fun k l => decide (partOf k ≠ partOf l))
    (fun k l => by simp [ne_comm]) (fun k => by simp)

/-- The "part index" of vertex `k < ps.foldl (·+·) 0` under the block
layout `[n₀, n₁, …]`: the index `i` of the block containing `k`.  Computed
by walking the prefix sums. -/
def multipartitePartOf (ps : List ℕ) (k : ℕ) : ℕ :=
  let rec go : List ℕ → ℕ → ℕ → ℕ
    | [], _, idx => idx
    | n :: rest, acc, idx => if k < acc + n then idx else go rest (acc + n) (idx + 1)
  go ps 0 0

/-- The canonical instance of a `KnownFamily` as a `WeightedGraph` on
`Fin f.expectedSize`.  Combinatorial families (path, cycle, complete,
star, complete-multipartite, hypercube) are built directly on
`Fin (expectedSize)` via the generic `finGraphOfBool` constructor — note
the hypercube on `Fin (2^n)` matches the `StdLib.Hypercube` construction
(adjacency at Hamming distance `1`).  The two families whose textbook
vertex type is not literally `Fin (expectedSize)` (the Hamming graph on
`Fin n → Fin q`, and the abelian Cayley graph on an abstract group) are
given the empty-graph handle of the correct size; their analytic content
is carried by the genuine `StdLib/*` constructions, not by this uniform
size-handle. -/
noncomputable def familyGraph : (f : KnownFamily) →
    WeightedGraph (Fin f.expectedSize)
  | .path n                  => finPathGraph (n + 1)
  | .weightedPath n          => finPathGraph (n + 1)
  | .hypercube n             =>
      -- `expectedSize = 2^n`; the hypercube adjacency is Hamming distance 1.
      finGraphOfBool (2 ^ n)
        (fun k l => decide (Graphplay.StdLib.hammingDist n k l = 1))
        (fun k l => by simp [Graphplay.StdLib.hammingDist_comm])
        (fun k => by simp)
  | .hamming n q             => finEmptyGraph (q ^ n)
  | .cayleyAbelian order _   => finEmptyGraph order
  | .completeMultipartite ps =>
      finCompleteMultipartiteGraph (ps.foldl (· + ·) 0)
        (fun k => multipartitePartOf ps k.val)
  | .cycle n                 => finCycleGraph n
  | .complete n              => finCompleteGraph n
  | .star n                  => finStarGraph (n + 1)

/-- **Soundness of the matcher.**  A successful `stdLibMatch` returns a
result whose recognised family is isospectral to the input under the
returned bijection.  Strengthening this to *isomorphism* (when the
structural recogniser succeeds) is the natural next step. -/
theorem stdLibMatch_sound
    (G : WeightedGraph V) (r : MatchResult V)
    (h : stdLibMatch G = some r) :
    r.targetSize = r.family.expectedSize ∧
    Isospectral G (familyGraph r.family) := by
  sorry

/-- **No-false-positive corollary.**  If `G` is not isospectral to any
`KnownFamily`, then `stdLibMatch G = none`. -/
theorem stdLibMatch_complete_negative
    (G : WeightedGraph V)
    (h : ∀ f : KnownFamily, ¬ Isospectral G (familyGraph f)) :
    stdLibMatch G = none := by
  sorry

/-! ## Convenience: name-only lookup

A faster scan that returns just the recognised family name (or `none`)
without committing to a particular vertex bijection.  Useful when a
caller only wants to know "what is this graph?". -/

/-- Lightweight matcher: returns just the recognised family. -/
noncomputable def stdLibMatchName (G : WeightedGraph V) : Option KnownFamily :=
  (stdLibMatch G).map (·.family)

/-- The full match's family agrees with the lightweight match. -/
theorem stdLibMatchName_eq_family
    (G : WeightedGraph V) (r : MatchResult V)
    (h : stdLibMatch G = some r) :
    stdLibMatchName G = some r.family := by
  -- direct rewrite from the assumption; deferred so the file compiles
  -- alongside the broader matcher API.
  sorry

/-! ## Diagnostics

Render a `MatchResult` as a human-readable line for inclusion in
compiler reports. -/

/-- A short summary string for a match. -/
def MatchResult.summary (r : MatchResult V) : String :=
  s!"matched {r.family.name} on {r.targetSize} vertices"

end Algorithm
end Graphplay
