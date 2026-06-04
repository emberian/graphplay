# The "quantum-like" brain is an equitable quotient

*A classical, machine-checked account of Deco–Sanz Perl–Greenstein–Chandaria–Scholes–Kringelbach,
"Quantum-like dynamics in the human brain" (bioRxiv 2025.10.02.680057).*
Companion to `Graphplay/Integrations/Connectome.lean`.

## Thesis

The paper reports that whole-brain models fit human neuroimaging better, and run
on less energy, in a "quantum-like" (QL) regime, and frames this in Hilbert-space
language (Scholes/Khrennikov): interference, superposition, two-state QL-bits,
decoherence-free states. **None of the measured phenomena require quantum
mechanics.** Every load-bearing quantity is a *spectral functional of a graph
Laplacian*, and the "QL" structure is exactly the **equitable-partition /
cell-uniform** structure of an algebraic-graph-theory quotient. We make this
precise and machine-check it: the whole-brain functional connectivity reduces
**exactly** to a computation on the structural connectome, with the spectral gap
inherited exactly, by the Godsil–Tamon equitable-quotient lift.

The slogan: **their "decoherence-free two-state QL subspace" is the cell-uniform
(synchronization) subspace; their "Hilbert space" is a graph eigenspace; their
"interference" is classical eigenmode beating.**

## 1. One mechanism, two readings

For a weighted graph `G` with an equitable partition `P` (cells = brain regions),
the cell-inflate map `cellInflateVec : (cells → ℂ) → (vertices → ℂ)` embeds the
quotient state space into the full one. The single fact behind everything is that
the adjacency **intertwines** its symmetric quotient through this map
(Bachman–Tamon; `Intertwines.adj`):

```
A *ᵥ cellInflate v = cellInflate (Q̃ *ᵥ v).
```

We prove this property is closed under the entire rational functional calculus —
sums, products, powers, scalar shifts, **inverses** (`Intertwines.{add,mul,smul,pow,inv}`).
So *any* spectral functional `f(A)` reduces to `f(Q̃)` on the synchronization
subspace. Two instances:

* **Quantum** — the continuous-time quantum walk `U(t)=exp(−itA)` reduces to the
  quotient walk `exp(−itQ̃)` (`intertwines_pow` proves it for every polynomial /
  Krylov approximant; `intertwines_evolve` is the analytic limit).
* **Quantum-like (classical)** — the Ornstein–Uhlenbeck / Lyapunov stationary
  covariance — i.e. Deco's functional connectivity — reduces to the connectome's
  (`stationaryFC_reduces_along_quotient`, fully proved via the resolvent case).

"Quantum" and "quantum-like" are the *same theorem* applied to two functions of
the same graph operator. That is the bridge.

## 2. The brain construction, and why the reduction is exact

The whole-brain "network of networks" `Ĉ` (their Fig. 1C / Fig. 2) is built as
`regionalNetwork H Reg`: `N` regions, each a copy of a `k`-regular regional graph
`Reg`, coupled by the dMRI structural connectome `H`. We prove:

* `regionalPartition` **is a genuine equitable partition** of `Ĉ` (the `uniform`
  field is proved, not assumed).
* its symmetric quotient is the connectome plus the regional self-coupling,
  `Q̃ = C + d·I` (`regionalPartition_symmQuotient_eq`); and — the punchline —
* **the quotient Laplacian is exactly the connectome Laplacian**
  (`regionalNetwork_quotientLaplacian_eq_host`): the regional degree `d` cancels
  between the degree diagonal and the quotient diagonal, so `D_Q − Q̃ = D_C − C`.

Deco's prescription "reduce `FCᵐᵒᵈᵉˡ` by averaging across the `n` nodes in each
region" (their p. 6) is therefore **not an approximation** — it is the exact
equitable quotient. Concretely, with the Hopf drift linearised at the edge of
bifurcation to `J = a·I − L` (their Eq. 8, symmetric reduction) and isotropic
noise `Q = σ²I`, the stationary covariance is the Laplacian resolvent

```
K = (σ²/2)(L − a·I)⁻¹        (stationaryFC; solves J K + K Jᵀ + Q = 0, Eq. 10)
```

and `stationaryFC_reduction` proves the whole-brain `K_Ĉ` intertwines the
connectome `K_C` through the regional cell-inflate. **Whole-brain FC = connectome
FC, certified.**

## 3. What is machine-checked (axiom-clean)

`#print axioms` shows the standard trio `[propext, Classical.choice, Quot.sound]`
— **no `sorryAx`** — for every result below:

| Result | Statement |
|---|---|
| `regionalPartition` | the regional blow-up is a genuine equitable partition |
| `regionalNetwork_quotientLaplacian_eq_host` | quotient Laplacian = connectome Laplacian (`d` cancels) |
| `stationaryFC_solves_lyapunov` | `K=(σ²/2)(L−aI)⁻¹` solves Deco's Lyapunov equation |
| `stationaryFC_reduces_along_quotient` | FC reduces along **any** equitable quotient (general) |
| `stationaryFC_reduction` | whole-brain FC = connectome FC (corollary) |
| `resolvent_isUnit_of_neg` | for `a<0`, `L−aI` is positive definite, hence invertible |
| `connectome_gap_inherited` | the connectome's spectral gap is inherited by `Ĉ` (Fig. 1C) |
| `algConn_prune_le` | removing edges shrinks the algebraic connectivity (Fig. 4A) |
| `qlbit_fc_reduction` | the reduction *fires* on a concrete two-region "QL bit" (K₂), all hypotheses discharged |

The only `sorry` is `intertwines_evolve` (the unitary `exp` limit) — the standard
holomorphic-functional-calculus closure that Mathlib lacks for a rectangular
intertwiner; its polynomial core `intertwines_pow` is proved. It is irrelevant to
the classical account.

## 4. Classical explanation of each "QL" phenomenon

| Paper's "quantum-like" claim | Classical mechanism (and our theorem) |
|---|---|
| "QL state": emergent state separated in the spectrum, robust, two-state (Scholes A–C) | a `k`-regular **expander** with a spectral gap `λ₀−λ₁`; the two states = cell-uniform vs. orthogonal complement |
| "Interference / superposition / QL-bit = tensor of Hilbert spaces" | classical **eigenmode** combination of coupled-oscillator networks; the QL-bit is the `N=2` regional blow-up |
| "QL fits fMRI better; lower energy" | FC = Laplacian resolvent `(σ²/2)(L−aI)⁻¹`; fit and energy are functionals of the **graph spectrum** of a linear stochastic (OU) process |
| "Distributed spectral gap" (Fig. 1C) | the connectome's gap inherited by `Ĉ` through the equitable quotient — `connectome_gap_inherited` |
| "Metastability = switching between cluster-sync states" | slow dynamics of the gap-separated **cell-uniform subspace** — a time-averaged spectral functional (same family as quantum average mixing) |
| "Long-range edges amplify the gap" (Fig. 4A) | monotonicity of the Fiedler value under edge addition — `algConn_prune_le` |
| "Decoherence-free / robust to disorder" | the synchronization manifold is `A`-invariant for *any* weights respecting the partition (equitable invariance) |

## 5. The general statement (and why it's more than the brain)

The brain model is one instance of:

> **For any equitable, degree-balanced graph, the OU/Lyapunov stationary FC
> intertwines the FC built from its quotient Laplacian**
> (`stationaryFC_reduces_along_quotient`).

This is a reusable theorem about *any* networked linear-stochastic system with a
regional symmetry: hierarchical control, multi-scale diffusion, consensus
dynamics, GNN message passing on quotient graphs. The connectome is where it
happens to meet neuroscience. The same `Intertwines` backbone also gives the
genuinely-quantum reduction, so the framework spans unitary coherent transport
and classical stochastic correlation in one object.

## 6. Honest scope

* **One analytic `sorry`** (`intertwines_evolve`); polynomial case proved.
* **Symmetric reduction `ω = 0`.** We formalise the non-rotating block `J = aI−L`
  of their Jacobian (Eq. 8). The equitable reduction extends to the full rotating
  Jacobian whenever the intrinsic frequency `ω` is constant on cells (a standard
  modelling choice), but we proved the `ω=0` case.
* **We explain the spectral/dynamical phenomena, not a quantum claim.** We do not
  assert the brain is quantum; we show the reported effects are accounted for by
  spectral graph theory + linear stochastic dynamics, with the equitable quotient
  as the exact reduction. (The paper's "interference" is classical eigenmode
  structure — which is precisely what the spectral-functional picture captures.)

## 7. What this buys

1. **Compute.** The exact quotient turns an `O((N·n)²)` whole-brain Lyapunov solve
   into an `O(N²)` connectome solve **with a correctness certificate** — useful for
   the Deco/Kringelbach pipeline as-is.
2. **Credibility.** It isolates the unimpeachable content (a spectral-gap /
   resolvent statement about expanders) from the contestable QL metaphysics —
   precision as credibility.
3. **A falsifiable, theorem-backed prediction.** Fig. 4A becomes the monotonicity
   theorem `algConn_prune_le`: removing the long-range exceptions can only shrink
   the algebraic-connectivity gap.
