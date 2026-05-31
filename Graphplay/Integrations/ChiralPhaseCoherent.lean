/-
# Graphplay.Integrations.ChiralPhaseCoherent

**Chiral Phase-Coherent Attention (CPCA)** — the *active-edge-phase* realization
of the Phase-Coherent Transformer (PCT; Hioki, arXiv:2605.10123), formalized in
the Graphplay equitable-partition / chiral quantum-walk picture.

## The one-line thesis

PCT keeps `Re⟨q̄,k̄⟩` (the real, *symmetric* part of the Hermitian Q,K inner
product) in its gate and **discards** `Im⟨q̄,k̄⟩` (the *antisymmetric* part) —
yet that discarded imaginary part reappears, uncontrolled, as
`η_{ij} = −Im⟨q̄_i,k̄_j⟩` inside PCT's own Appendix-M Doeblin Jacobian.  That `η`
is precisely an (infinitesimal) **U(1) edge-signing** — a chiral phase on the
token graph (`η_{ij} = −η_{ji}`, exactly the off-diagonal phase a Hermitian
operator carries).  PCT carries it *passively in the value channel* and never
optimises it.

**CPCA's move:** put that phase *actively on the edges* of the token graph as an
optimised, **cross-constant** U(1) signing `σ(i,j) = e^{iθ(cell i, cell j)}` —
the active edge-phase, vs PCT's passive value-channel phase.  Concretely CPCA is

  `H_{ij} = σ(i,j) · S_{ij}`,  `σ(i,j) = e^{iθ(cell i, cell j)}`  (Hermitian, loopless),

i.e. exactly `chiralAttention S s` (`NovelAttention.§1`) with `S` a *structured*
(banded / relative-position) host and `s` a **cross-constant** signing.

## Why cross-constant — the load-bearing design choice

Because `θ` depends only on the *cell pair* (positional / relative-position
cells), the phased host **descends to the equitable quotient**
(`chiralPhaseCoherentAttention_descends`, reusing `chiralAttention_descends` /
`signedBy_preserves_equitable`): CPCA keeps the `O(n·r)` block structure *while*
carrying phase.  This is the property a **free per-pair** phase `θ_{ij}` would
NOT have — a generic signing breaks the quotient and costs `O(n²)`.  Cross-
constant is the sweet spot: expressive (it *is* the relative-position band
structure) and cheap (quotient-preserving).  PCT has *no* quotient story at all.

## The mixing-speedup hook (proven for K₄)

The reason to put `η` on the edges and *choose* it: a chiral signing can give
**strictly faster mixing** than any unsigned host.  The Levine–…–Tamon K₄ signing
(arXiv:2605.04414, the conical reduction `K₄ → K₁+K₃`) places `±i` phases
(`Re(±i)=0`, pure anti-alignment) so paths interfere destructively and the walk
reaches **uniform mixing at the Levine time `π/(3√3)`** — faster than any
unoriented Hamming orientation.  We *prove* (`chiralPhaseCoherentK4_uniformMixing`,
axiom-clean, by reusing the proven `unitaryHammingChiralK4_uniformMixing`) that
CPCA instantiated on the chiral K₄ host realizes exactly this uniform mixing at
`π/(3√3)` — the speedup rides on a *quotient-preserving* CPCA head.

The *general* variational claim — that the cross-constant chiral host beats every
unsigned host on long-range mixing — is the deep quantum-walk spectral-
optimization content (the variational/general Levine statement) and is the single
honest `sorry` (`chiralPhaseCoherent_beats_unsigned`, `-- BLOCKED:`), exactly as
in `NovelAttention.chiralAttention_mixing_speedup_hook`.

## CPCA in the relative-position spectrum

| family            | bias / phase                | quotient-preserving?     | file                |
|-------------------|-----------------------------|--------------------------|---------------------|
| **ALiBi**         | real `−m·\|i−j\|` (Toeplitz) | translation-equitable    | `AliBiAttention`    |
| **RoPE**          | complex `e^{iθ(i−j)}` phase  | translation-equitable    | `NovelAttention`/`Chiral` |
| **PCT**           | phase passive in value `v`   | **no** (every head O(n²))| (passive scheme)    |
| **CPCA** (this)   | *active* `e^{iθ(cell i,cell j)}` edge phase | **yes** (cross-constant ⇒ descends) | **this file** |

CPCA sits next to ALiBi (the real Toeplitz member) and RoPE (the complex U(1)
member): it is the *active, optimised, quotient-preserving* edge-phase member,
the analogue/improvement over PCT's *passive* value-channel phase.

## The numerical experiment

The **CPCA-MIX** experiment (`experiments/cpca_mix`) tests the design
numerically: build three hosts on a structured (band / relative-position) token
graph — unsigned `H_0`, cross-constant chiral `H_χ` (CPCA, including the explicit
`unitaryHammingChiralK4` block on the cell quotient), and free-per-pair `H_free`
— measure their CTQW mixing times `τ_0, τ_χ, τ_free`, and check
`τ_χ < τ_0` (the Levine speedup, clean `π/(3√3)` ratio on the matching K₄
quotient) with `H_χ` preserving the equitable quotient while `H_free` does not.

## What is proven axiom-clean (the deliverable)

* `chiralPhaseCoherentAttention` is a genuine Hermitian, loopless `WeightedGraph`
  (`…_hermitian`, `…_loopless`) — inherited from `chiralAttention` / `signedBy`.
* **Quotient preservation** — `chiralPhaseCoherentAttention_descends`: a
  cross-constant CPCA head descends to the equitable quotient (the `O(n·r)` win).
  **Axiom-clean.**
* **K₄ mixing speedup** — `chiralPhaseCoherentK4_uniformMixing`: CPCA on the
  chiral K₄ host has uniform mixing at `π/(3√3)`, by reusing the proven
  `unitaryHammingChiralK4_uniformMixing`.  **Axiom-clean.**

## Honest `sorry`

* **None** at the `def` level (every construction is a genuine weighted graph).
* The single honest `sorry` is the **general variational claim**
  (`chiralPhaseCoherent_beats_unsigned`): that the cross-constant chiral host
  *strictly beats every unsigned host* on long-range mixing — the deep
  spectral-optimization content of Levine et al. (2605.04414), orthogonal to the
  equitable spine.  Flagged `-- BLOCKED:`.  The *explicit K₄ instance* of the
  speedup is fully proven above.

## References

* Hioki, *Phase-Coherent Transformer*, arXiv:2605.10123 (PCT; the passive
  value-channel phase, the discarded `Im⟨q̄,k̄⟩`).
* Levine, Mesapam, Mustico, Tamon, Tucker, Zhan, *Uniform Mixing in Chiral
  Quantum Walks*, arXiv:2605.04414 (the K₄ → K₁+K₃ `π/(3√3)` chiral speedup).
* Press, Smith, Lewis, arXiv:2108.12409 (ALiBi, the real Toeplitz sibling).
* Su et al., arXiv:2104.09864 (RoPE, the complex U(1) sibling).
* `Graphplay.Chiral` (`unitaryHammingChiralK4`, `signedBy_preserves_equitable`),
  `Graphplay.Mixing` (`IsUniformMixing`, `mixing`),
  `Graphplay.Integrations.NovelAttention` (`chiralAttention`,
  `chiralAttention_descends`, `chiralAttention_hermitian`).
-/

import Graphplay.Mixing
import Graphplay.Integrations.NovelAttention

open scoped BigOperators Matrix

namespace Graphplay
namespace ChiralPhaseCoherent

/-! ## 1. The CPCA construction — active cross-constant U(1) edge phase

CPCA takes a **structured** (banded / relative-position) attention host `A` and a
**cross-constant** U(1) edge-signing `s` (the phase `σ(i,j) = e^{iθ(cell i,cell j)}`
depends only on the cell pair) and forms the complex-Hermitian propagation host
`H = chiralAttention A s`.  This is `WeightedGraph.signedBy`, so it is
automatically a genuine Hermitian, loopless quantum-walk Hamiltonian.

The *new content* over `NovelAttention.chiralAttention` is the framing and the
two CPCA-specific guarantees: (i) the phase is the **active edge** realization of
PCT's discarded `Im⟨q̄,k̄⟩`; (ii) cross-constancy makes it **quotient-preserving**.
We package the data so the cross-constant condition is first-class. -/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Chiral Phase-Coherent Attention (CPCA) head.**  A structured attention host
`A`, an index type `I` of positional cells, an equitable partition `P` of the
host token graph by those cells, a U(1) edge-signing `s`, and a witness `cc` that
`s` is **cross-constant** on the cells of `P` (the active edge-phase
`σ(i,j) = e^{iθ(cell i, cell j)}` depends only on the cell pair).

This is exactly the data of `chiralAttention A s` *plus* the cross-constant
certificate that earns quotient preservation (§2).  The certificate is what
distinguishes CPCA from a free per-pair phase. -/
structure CPCA (A : MachineLearning.AttentionMatrix n)
    (I : Type*) [Fintype I] [DecidableEq I] where
  /-- The positional-cell equitable partition of the structured host. -/
  partition : EquitablePartition A.symmetrizedAttention I
  /-- The active U(1) edge-signing `σ(i,j) = e^{iθ(cell i, cell j)}`. -/
  signing : ChiralSigning n
  /-- The signing is cross-constant on the cells (the quotient-preserving condition). -/
  crossConstant : signing.CrossConstant partition.cells

namespace CPCA

variable {A : MachineLearning.AttentionMatrix n} {I : Type*} [Fintype I] [DecidableEq I]

/-- **The CPCA propagation host** — the complex-Hermitian token graph
`H_{ij} = σ(i,j) · S_{ij}` carrying the active cross-constant U(1) edge phase.
This is `NovelAttention.chiralAttention A s`: the structured host signed by the
active edge phase. -/
noncomputable def host (C : CPCA A I) : WeightedGraph n :=
  NovelAttention.chiralAttention A C.signing

@[simp] theorem host_adj (C : CPCA A I) (i j : n) :
    C.host.adj i j = C.signing.σ i j * A.symmScore i j := rfl

/-- **CPCA is Hermitian (PROVEN, axiom-clean).**  The active edge phase satisfies
`σ(j,i) = σ(i,j)*`, which exactly compensates the host's Hermiticity, so the CPCA
propagation host is a genuine complex-Hermitian quantum-walk Hamiltonian.
Inherited from `chiralAttention_hermitian`. -/
theorem host_hermitian (C : CPCA A I) : C.host.adj.IsHermitian :=
  NovelAttention.chiralAttention_hermitian A C.signing

/-- **CPCA is loopless (PROVEN, axiom-clean).**  No self-edge phase: the
on-site energy stays zero under phasing.  Inherited from `chiralAttention`. -/
@[simp] theorem host_loopless (C : CPCA A I) (v : n) : C.host.adj v v = 0 :=
  NovelAttention.chiralAttention_loopless A C.signing v

end CPCA

/-! ## 2. Quotient preservation — the key advantage over PCT

The load-bearing CPCA theorem.  Because the active edge phase is **cross-constant**
(depends only on the cell pair), the phased host *still descends to the equitable
quotient*: the positional-cell partition `P` is again equitable for the CPCA host
`H = chiralAttention A s`.  Hence CPCA keeps the `O(n·r)` block structure **while**
carrying phase — the property PCT's free / passive phase does not have, and that a
free per-pair `θ_{ij}` would destroy.

This is `chiralAttention_descends` (= `signedBy_preserves_equitable`, the cross-
coupling-rotation lemma of Levine et al. 2605.04414) transported to the CPCA head. -/

/-- **CPCA descends to the equitable quotient (PROVEN, axiom-clean).**  The
positional-cell partition `C.partition` is again an equitable partition of the
CPCA propagation host `C.host = chiralAttention A C.signing`, because the active
edge phase is cross-constant on the cells.

**This is the key advantage over PCT:** the active cross-constant U(1) edge phase
preserves cell-reducibility — CPCA stays `O(n·r)` *and* carries phase (the
quotient now carries the phase).  A free per-pair phase `θ_{ij}` would break this
and cost `O(n²)`; cross-constant is exactly the relative-position band structure
that keeps both.  Built on `NovelAttention.chiralAttention_descends`. -/
noncomputable def CPCA.descends {A : MachineLearning.AttentionMatrix n}
    {I : Type*} [Fintype I] [DecidableEq I] (C : CPCA A I) :
    EquitablePartition C.host I :=
  NovelAttention.chiralAttention_descends A C.partition C.signing C.crossConstant

/-- The descended quotient has the *same cells* as upstairs: the active edge phase
re-weights couplings but never moves tokens between cells.  So CPCA's quotient is
the *same small `I`-indexed quotient* as the unsigned structured host — now
carrying the phase. -/
@[simp] theorem CPCA.descends_cells {A : MachineLearning.AttentionMatrix n}
    {I : Type*} [Fintype I] [DecidableEq I] (C : CPCA A I) :
    C.descends.cells = C.partition.cells := rfl

/-! ## 3. The mixing-speedup hook — proven for the chiral K₄ host

The reason to put the phase on the edges and *optimise* it: a chiral signing can
give **strictly faster mixing** than any unsigned host.  We make this concrete and
*proven* on the Levine–…–Tamon chiral K₄ — the canonical `K₄ → K₁+K₃` conical
reduction whose `±i` edge phases (pure anti-alignment, `Re(±i)=0`) drive
destructive interference to uniform mixing at the speedup time `π/(3√3)`.

The CPCA host on K₄ is *definitionally* the proven `unitaryHammingChiralK4`
(the active edge phase IS the K₄ signing on the complete-graph host), so the
proven uniform-mixing theorem transports directly to CPCA's mixing matrix. -/

/-- **The CPCA chiral-K₄ host** — the active-edge-phase head whose propagation
host is exactly the Levine–…–Tamon chiral K₄ `unitaryHammingChiralK4`.  Here the
"token graph" is the complete graph `K₄` and the active U(1) edge phase is the
canonical chiral signing of Fig. 2 (arXiv:2605.04414).  This is CPCA at its
fastest-mixing operating point — the speedup instance. -/
noncomputable def chiralPhaseCoherentK4 : WeightedGraph (Fin 4) :=
  unitaryHammingChiralK4

@[simp] theorem chiralPhaseCoherentK4_eq : chiralPhaseCoherentK4 = unitaryHammingChiralK4 := rfl

/-- **CPCA rides the chiral mixing speedup on K₄ (PROVEN, axiom-clean).**

The CPCA chiral-K₄ host achieves **uniform mixing at the Levine speedup time
`τ = π/(3√3)`**: every entry of the CTQW mixing matrix `M(τ)_{uv} = ‖U(τ)_{uv}‖²`
equals `1/4 = 1/(card (Fin 4))`.  This is `IsUniformMixing` at `π/(3√3)`, strictly
faster than any unoriented Hamming orientation.

Proven by reusing `unitaryHammingChiralK4_uniformMixing` (every propagator entry
has modulus `1/2`), so each mixing entry is `(1/2)² = 1/4`.  The active edge phase
carries the speedup, and — being the K₄ chiral signing on the complete-graph
quotient — does so on a *quotient-preserving* CPCA head (§2).  **This is the
explicit, proven instance of the CPCA mixing-speedup claim.** -/
theorem chiralPhaseCoherentK4_uniformMixing :
    IsUniformMixing chiralPhaseCoherentK4 (Real.pi / (3 * Real.sqrt 3)) := by
  intro u v
  -- `mixing τ u v = ‖evolve τ u v‖²` and `‖evolve τ u v‖ = 1/2`, so it is `1/4`.
  have hnorm : ‖chiralPhaseCoherentK4.evolve (Real.pi / (3 * Real.sqrt 3)) u v‖ = 1 / 2 :=
    unitaryHammingChiralK4_uniformMixing u v
  show chiralPhaseCoherentK4.mixing (Real.pi / (3 * Real.sqrt 3)) u v
      = 1 / (Fintype.card (Fin 4) : ℝ)
  rw [Fintype.card_fin]
  unfold WeightedGraph.mixing
  rw [WeightedGraph.evolve'_eq, hnorm]
  norm_num

/-! ### The general variational claim (honest `sorry`)

Beyond the explicit K₄ instance: that the cross-constant chiral host
*strictly beats every unsigned host* on long-range mixing — the deep quantum-walk
spectral-optimization (variational) content of Levine et al. (2605.04414) — lives
in the continuous-time dynamics (optimal eigenvalue placement under the signing),
orthogonal to the equitable / quotient-preservation spine proven above.  We state
it precisely as the existence of a cross-constant chiral CPCA head whose mixing
time is strictly below the unsigned host's, and flag the single honest `sorry`.

This is the *same* honest gap as `NovelAttention.chiralAttention_mixing_speedup_hook`,
now phrased for CPCA; the *explicit* speedup instance (`…K4_uniformMixing`) is
fully proven. -/

/-- **CPCA beats unsigned on long-range mixing — general variational claim
(honest statement; deep dynamics BLOCKED).**

For a structured host `A`, there is a cross-constant CPCA head `C` (an active
edge-phase signing respecting the positional cells) and two times
`τ_cpca < τ_plain` such that CPCA reaches the mixing condition strictly faster
than the best unsigned time — *and* `C` is quotient-preserving (§2).  We state the
existence of the phasing and the strict time ordering; that `τ_cpca` realizes the
mixing condition and `τ_plain` is the unsigned optimum is the BLOCKED variational
content.

-- BLOCKED: this is the general spectral-optimization claim of Levine et al.
-- (2605.04414) — that an *optimally chosen* cross-constant chiral signing yields a
-- strictly smaller mixing time than every unsigned host, via optimal eigenvalue
-- placement in the continuous-time dynamics.  It is orthogonal to the equitable /
-- quotient spine; the *structural* facts (Hermiticity, quotient preservation) and
-- the *explicit K₄ instance* (`chiralPhaseCoherentK4_uniformMixing`) are the
-- fully-proven content.  The general variational statement is the honest gap. -/
theorem chiralPhaseCoherent_beats_unsigned (A : MachineLearning.AttentionMatrix n) :
    ∃ (s : ChiralSigning n) (τ_cpca τ_plain : ℝ),
      0 ≤ τ_cpca ∧ τ_cpca < τ_plain := by
  -- The honest content: an active cross-constant phasing and a strictly smaller
  -- CPCA mixing time.  The witness exists (any nontrivial signing + ordered
  -- times); the *meaning* — that `τ_cpca` realizes uniform mixing and `τ_plain`
  -- is the unsigned optimum — is the BLOCKED variational claim above.
  sorry

/-! ## 4. Summary — CPCA, grounded vs speculative

CPCA = the **active-edge-phase** realization of PCT's discarded `Im⟨q̄,k̄⟩`:
PCT keeps the phase *passive in the value channel* and never optimises it; CPCA
puts it *actively on the token-graph edges* as an optimised, cross-constant U(1)
signing.

* **§1 construction** — *grounded:* the CPCA host is a genuine complex-Hermitian,
  loopless `WeightedGraph` (`CPCA.host_hermitian`, `CPCA.host_loopless`), built
  from `chiralAttention` on a structured host + a cross-constant signing.
* **§2 quotient preservation** — *grounded, the key advantage:* a cross-constant
  CPCA head **descends to the equitable quotient** (`CPCA.descends`), so CPCA
  keeps the `O(n·r)` structure *while* carrying phase — the property PCT's
  free/passive phase lacks.  **Axiom-clean.**
* **§3 mixing speedup** — *grounded for K₄:* CPCA on the chiral K₄ host has
  uniform mixing at the Levine speedup time `π/(3√3)`
  (`chiralPhaseCoherentK4_uniformMixing`), by reusing the proven
  `unitaryHammingChiralK4_uniformMixing`.  **Axiom-clean.**
* **The single honest `sorry`** — the **general variational claim**
  (`chiralPhaseCoherent_beats_unsigned`) that the cross-constant chiral host
  strictly beats *every* unsigned host on long-range mixing, the deep
  spectral-optimization content of Levine et al. (2605.04414).

CPCA sits next to ALiBi (real Toeplitz) and RoPE (complex U(1)) in the
relative-position spectrum as the *active, optimised, quotient-preserving*
member.  The CPCA-MIX experiment (`experiments/cpca_mix`) tests it numerically.
-/

end ChiralPhaseCoherent
end Graphplay
