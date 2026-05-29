/-
# Graphplay.Product

First-class **graph products** on `WeightedGraph` (structural blocker #3).

Until now graphplay has carried the Cartesian / tensor / strong products only as
`GraphBundle` corners.  This module promotes them to first-class operations on
the `WeightedGraph` data type over the product vertex set `V × W`, together with
their genuine spectral / regularity content:

* `cartesianProduct G H`  — the Cartesian (□) product = **Kronecker sum**
  `A ⊗ I + I ⊗ B`; eigenvalues add.
* `tensorProduct G H`      — the weak / direct (×) product = **Kronecker product**
  `A ⊗ₖ B`; eigenvalues multiply.
* `strongProduct G H`      — the strong (⊠) product = Cartesian + tensor terms;
  eigenvalues `λ + μ + λμ` on common eigenvectors.

For each we prove `herm` and `loopless` genuinely (no `sorry` on the structure
fields), give the entrywise / Kronecker adjacency identities, the
eigenvector-construction lemmas (`tensorProduct_mulVec`, `cartesianProduct_mulVec`,
`strongProduct_mulVec`) that are the real "spectrum multiplies / adds" core, and
the regularity-degree formulas.

Reference: Ge–Greenberg–Pérez–Tamon, *Perfect state transfer, graph products and
equitable partitions* (arXiv:1009.1340).
-/

import Graphplay.Weighted
import Mathlib.LinearAlgebra.Matrix.Kronecker

open scoped Matrix Kronecker

namespace Graphplay

namespace WeightedGraph

variable {V : Type*} {W : Type*}
variable [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-! ## The Cartesian (□) product — Kronecker sum -/

/-- The **Cartesian product** `G □ H` on `V × W`.  Two vertices are adjacent when
they agree on one coordinate and are adjacent in the other factor; as a matrix
this is the *Kronecker sum* `A ⊗ I + I ⊗ B`.  Concretely

`adj (v₁,w₁) (v₂,w₂) = (if w₁ = w₂ then G.adj v₁ v₂ else 0)
                       + (if v₁ = v₂ then H.adj w₁ w₂ else 0)`. -/
def cartesianProduct (G : WeightedGraph V) (H : WeightedGraph W) :
    WeightedGraph (V × W) where
  adj := fun p q =>
    (if p.2 = q.2 then G.adj p.1 q.1 else 0) + (if p.1 = q.1 then H.adj p.2 q.2 else 0)
  herm := by
    -- conjugate-transpose of an entrywise sum of two Hermitian-symmetric terms.
    ext p q
    simp only [Matrix.conjTranspose_apply, star_add]
    congr 1
    · -- star (if q.2 = p.2 then G.adj q.1 p.1 else 0) = if p.2 = q.2 then G.adj p.1 q.1 else 0
      by_cases h : p.2 = q.2
      · rw [if_pos h, if_pos h.symm]; exact G.herm.apply p.1 q.1
      · rw [if_neg h, if_neg (fun e => h e.symm), star_zero]
    · by_cases h : p.1 = q.1
      · rw [if_pos h, if_pos h.symm]; exact H.herm.apply p.2 q.2
      · rw [if_neg h, if_neg (fun e => h e.symm), star_zero]
  loopless := by
    intro v
    simp [G.loopless, H.loopless]

@[simp]
theorem cartesianProduct_adj (G : WeightedGraph V) (H : WeightedGraph W)
    (p q : V × W) :
    (cartesianProduct G H).adj p q =
      (if p.2 = q.2 then G.adj p.1 q.1 else 0) + (if p.1 = q.1 then H.adj p.2 q.2 else 0) :=
  rfl

/-- Entrywise form of the Cartesian-product adjacency on explicit coordinates. -/
theorem cartesianProduct_adj_eq (G : WeightedGraph V) (H : WeightedGraph W)
    (v₁ w₁ v₂ w₂) :
    (cartesianProduct G H).adj (v₁, w₁) (v₂, w₂) =
      (if w₁ = w₂ then G.adj v₁ v₂ else 0) + (if v₁ = v₂ then H.adj w₁ w₂ else 0) :=
  rfl

/-! ## The tensor (×) product — Kronecker product -/

/-- The **tensor / direct product** `G × H` on `V × W`: the entrywise Kronecker
product of the two adjacency matrices,
`adj (v₁,w₁) (v₂,w₂) = G.adj v₁ v₂ * H.adj w₁ w₂`. -/
def tensorProduct (G : WeightedGraph V) (H : WeightedGraph W) :
    WeightedGraph (V × W) where
  adj := G.adj ⊗ₖ H.adj
  herm := by
    -- `(A ⊗ₖ B)ᴴ = Aᴴ ⊗ₖ Bᴴ = A ⊗ₖ B`.
    show (G.adj ⊗ₖ H.adj)ᴴ = G.adj ⊗ₖ H.adj
    rw [Matrix.conjTranspose_kronecker, G.herm.eq, H.herm.eq]
  loopless := by
    intro v
    rw [Matrix.kronecker_apply, G.loopless, zero_mul]

@[simp]
theorem tensorProduct_adj (G : WeightedGraph V) (H : WeightedGraph W)
    (p q : V × W) :
    (tensorProduct G H).adj p q = G.adj p.1 q.1 * H.adj p.2 q.2 :=
  rfl

/-- The tensor-product adjacency *is* the Mathlib Kronecker product `A ⊗ₖ B`. -/
theorem tensorProduct_adj_eq (G : WeightedGraph V) (H : WeightedGraph W) :
    (tensorProduct G H).adj = G.adj ⊗ₖ H.adj :=
  rfl

theorem tensorProduct_adj_apply (G : WeightedGraph V) (H : WeightedGraph W)
    (v₁ w₁ v₂ w₂) :
    (tensorProduct G H).adj (v₁, w₁) (v₂, w₂) = G.adj v₁ v₂ * H.adj w₁ w₂ :=
  rfl

/-! ## The strong (⊠) product -/

/-- The **strong product** `G ⊠ H` on `V × W`: the sum of the Cartesian and the
tensor adjacency terms,
`adj (v₁,w₁) (v₂,w₂) = (if w₁ = w₂ then G.adj v₁ v₂ else 0)
                       + (if v₁ = v₂ then H.adj w₁ w₂ else 0)
                       + G.adj v₁ v₂ * H.adj w₁ w₂`. -/
def strongProduct (G : WeightedGraph V) (H : WeightedGraph W) :
    WeightedGraph (V × W) where
  adj := fun p q =>
    (if p.2 = q.2 then G.adj p.1 q.1 else 0) + (if p.1 = q.1 then H.adj p.2 q.2 else 0)
      + G.adj p.1 q.1 * H.adj p.2 q.2
  herm := by
    ext p q
    simp only [Matrix.conjTranspose_apply, star_add]
    congr 1
    · congr 1
      · by_cases h : p.2 = q.2
        · rw [if_pos h, if_pos h.symm]; exact G.herm.apply p.1 q.1
        · rw [if_neg h, if_neg (fun e => h e.symm), star_zero]
      · by_cases h : p.1 = q.1
        · rw [if_pos h, if_pos h.symm]; exact H.herm.apply p.2 q.2
        · rw [if_neg h, if_neg (fun e => h e.symm), star_zero]
    · -- star (G.adj q.1 p.1 * H.adj q.2 p.2) = G.adj p.1 q.1 * H.adj p.2 q.2
      rw [star_mul']
      rw [show star (G.adj q.1 p.1) = G.adj p.1 q.1 from G.herm.apply p.1 q.1,
          show star (H.adj q.2 p.2) = H.adj p.2 q.2 from H.herm.apply p.2 q.2]
  loopless := by
    intro v
    simp [G.loopless, H.loopless]

@[simp]
theorem strongProduct_adj (G : WeightedGraph V) (H : WeightedGraph W)
    (p q : V × W) :
    (strongProduct G H).adj p q =
      (if p.2 = q.2 then G.adj p.1 q.1 else 0) + (if p.1 = q.1 then H.adj p.2 q.2 else 0)
        + G.adj p.1 q.1 * H.adj p.2 q.2 :=
  rfl

theorem strongProduct_adj_eq (G : WeightedGraph V) (H : WeightedGraph W)
    (v₁ w₁ v₂ w₂) :
    (strongProduct G H).adj (v₁, w₁) (v₂, w₂) =
      (if w₁ = w₂ then G.adj v₁ v₂ else 0) + (if v₁ = v₂ then H.adj w₁ w₂ else 0)
        + G.adj v₁ v₂ * H.adj w₁ w₂ :=
  rfl

/-- The strong-product adjacency decomposes as the Cartesian plus the tensor
adjacency. -/
theorem strongProduct_adj_eq_cartesian_add_tensor (G : WeightedGraph V)
    (H : WeightedGraph W) :
    (strongProduct G H).adj =
      (cartesianProduct G H).adj + (tensorProduct G H).adj := by
  ext p q
  simp only [strongProduct_adj, cartesianProduct_adj, tensorProduct_adj, Matrix.add_apply]

/-! ## Eigenvector-construction lemmas (the spectral core)

If `x` is a `λ`-eigenvector of `G` and `y` a `μ`-eigenvector of `H`, then the
tensor vector `(v,w) ↦ x v * y w` is an eigenvector of each product, with
eigenvalue `λ·μ` (tensor), `λ+μ` (Cartesian), `λ+μ+λμ` (strong). -/

/-- The tensor vector built from `x : V → ℂ` and `y : W → ℂ`. -/
def tensorVec (x : V → ℂ) (y : W → ℂ) : V × W → ℂ := fun p => x p.1 * y p.2

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
@[simp]
theorem tensorVec_apply (x : V → ℂ) (y : W → ℂ) (p : V × W) :
    tensorVec x y p = x p.1 * y p.2 :=
  rfl

/-- **Tensor product multiplies eigenvalues.**  If `A x = λ x` and `B y = μ y`,
then `(A ⊗ₖ B)(x ⊗ y) = (λμ)(x ⊗ y)`. -/
theorem tensorProduct_mulVec (G : WeightedGraph V) (H : WeightedGraph W)
    {x : V → ℂ} {y : W → ℂ} {lam mu : ℂ}
    (hx : G.adj.mulVec x = lam • x) (hy : H.adj.mulVec y = mu • y) :
    (tensorProduct G H).adj.mulVec (tensorVec x y) = (lam * mu) • tensorVec x y := by
  funext p
  obtain ⟨v, w⟩ := p
  -- Expand mulVec over the product index set and factor the double sum.
  simp only [Matrix.mulVec, dotProduct, tensorProduct_adj, tensorVec, Pi.smul_apply,
    smul_eq_mul, Fintype.sum_prod_type]
  -- ∑ v', ∑ w', (G v v' * H w w') * (x v' * y w')
  --   = (∑ v', G v v' * x v') * (∑ w', H w w' * y w')
  have key : (∑ v', ∑ w', G.adj v v' * H.adj w w' * (x v' * y w'))
      = (∑ v', G.adj v v' * x v') * (∑ w', H.adj w w' * y w') := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun v' _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun w' _ => ?_)
    ring
  rw [key]
  -- The factor sums are exactly the eigenvalue equations evaluated at v, w.
  have hxv : (∑ v', G.adj v v' * x v') = lam * x v := by
    have := congrFun hx v
    simpa [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] using this
  have hyw : (∑ w', H.adj w w' * y w') = mu * y w := by
    have := congrFun hy w
    simpa [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] using this
  rw [hxv, hyw]
  ring

/-- **Cartesian product adds eigenvalues.**  If `A x = λ x` and `B y = μ y`,
then `(A ⊗ I + I ⊗ B)(x ⊗ y) = (λ+μ)(x ⊗ y)`. -/
theorem cartesianProduct_mulVec (G : WeightedGraph V) (H : WeightedGraph W)
    {x : V → ℂ} {y : W → ℂ} {lam mu : ℂ}
    (hx : G.adj.mulVec x = lam • x) (hy : H.adj.mulVec y = mu • y) :
    (cartesianProduct G H).adj.mulVec (tensorVec x y) = (lam + mu) • tensorVec x y := by
  funext p
  obtain ⟨v, w⟩ := p
  simp only [Matrix.mulVec, dotProduct, cartesianProduct_adj, tensorVec, Pi.smul_apply,
    smul_eq_mul, Fintype.sum_prod_type]
  -- ∑ v', ∑ w', ((if w = w' then G v v' else 0) + (if v = v' then H w w' else 0)) * (x v' * y w')
  -- Split the two `if` terms.
  have split : (∑ v', ∑ w',
        ((if w = w' then G.adj v v' else 0) + (if v = v' then H.adj w w' else 0))
          * (x v' * y w'))
      = (∑ v', ∑ w', (if w = w' then G.adj v v' else 0) * (x v' * y w'))
        + (∑ v', ∑ w', (if v = v' then H.adj w w' else 0) * (x v' * y w')) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun v' _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun w' _ => ?_)
    ring
  rw [split]
  -- First term: only w' = w survives, leaving (∑ v', G v v' x v') * y w = (λ x v) * y w.
  have t1 : (∑ v', ∑ w', (if w = w' then G.adj v v' else 0) * (x v' * y w'))
      = (lam * x v) * y w := by
    have inner : ∀ v', (∑ w', (if w = w' then G.adj v v' else 0) * (x v' * y w'))
        = G.adj v v' * (x v' * y w) := by
      intro v'
      rw [Finset.sum_eq_single w]
      · simp
      · intro w' _ hne
        simp [Ne.symm hne]
      · intro h; exact absurd (Finset.mem_univ w) h
    rw [Finset.sum_congr rfl (fun v' _ => inner v')]
    have hxv : (∑ v', G.adj v v' * x v') = lam * x v := by
      have := congrFun hx v
      simpa [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] using this
    calc (∑ v', G.adj v v' * (x v' * y w))
        = (∑ v', G.adj v v' * x v') * y w := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl (fun v' _ => by ring)
      _ = (lam * x v) * y w := by rw [hxv]
  -- Second term: only v' = v survives, leaving x v * (∑ w', H w w' y w') = x v * (μ y w).
  have t2 : (∑ v', ∑ w', (if v = v' then H.adj w w' else 0) * (x v' * y w'))
      = x v * (mu * y w) := by
    rw [Finset.sum_eq_single v]
    · have hyw : (∑ w', H.adj w w' * y w') = mu * y w := by
        have := congrFun hy w
        simpa [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] using this
      simp only [if_true]
      calc (∑ w', H.adj w w' * (x v * y w'))
          = x v * (∑ w', H.adj w w' * y w') := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun w' _ => by ring)
        _ = x v * (mu * y w) := by rw [hyw]
    · intro v' _ hne
      simp [Ne.symm hne]
    · intro h; exact absurd (Finset.mem_univ v) h
  rw [t1, t2]
  ring

/-- **Strong product:** common tensor eigenvectors have eigenvalue `λ + μ + λμ`. -/
theorem strongProduct_mulVec (G : WeightedGraph V) (H : WeightedGraph W)
    {x : V → ℂ} {y : W → ℂ} {lam mu : ℂ}
    (hx : G.adj.mulVec x = lam • x) (hy : H.adj.mulVec y = mu • y) :
    (strongProduct G H).adj.mulVec (tensorVec x y)
      = (lam + mu + lam * mu) • tensorVec x y := by
  have hdecomp := strongProduct_adj_eq_cartesian_add_tensor G H
  rw [hdecomp, Matrix.add_mulVec, cartesianProduct_mulVec G H hx hy,
    tensorProduct_mulVec G H hx hy, ← add_smul]

/-! ## Regularity / degree formulas -/

/-- Degree of a vertex in the Cartesian product is the sum of factor degrees. -/
theorem cartesianProduct_degree (G : WeightedGraph V) (H : WeightedGraph W)
    (p : V × W) :
    (cartesianProduct G H).degree p = G.degree p.1 + H.degree p.2 := by
  obtain ⟨v, w⟩ := p
  simp only [degree, cartesianProduct_adj, Fintype.sum_prod_type, Finset.sum_add_distrib]
  congr 1
  · -- ∑ v', ∑ w', if w = w' then G v v' else 0  =  ∑ v', G v v'
    rw [Finset.sum_comm]
    rw [Finset.sum_eq_single w]
    · simp
    · intro w' _ hne; simp [Ne.symm hne]
    · intro h; exact absurd (Finset.mem_univ w) h
  · -- ∑ v', ∑ w', if v = v' then H w w' else 0  =  ∑ w', H w w'
    rw [Finset.sum_eq_single v]
    · simp
    · intro v' _ hne; simp [Ne.symm hne]
    · intro h; exact absurd (Finset.mem_univ v) h

/-- The Cartesian product of `dG`-regular and `dH`-regular graphs is
`(dG + dH)`-regular. -/
theorem cartesianProduct_isRegular (G : WeightedGraph V) (H : WeightedGraph W)
    {dG dH : ℂ} (hG : G.isRegular dG) (hH : H.isRegular dH) :
    (cartesianProduct G H).isRegular (dG + dH) := by
  intro p
  rw [cartesianProduct_degree, hG p.1, hH p.2]

/-- Degree of a vertex in the tensor product is the product of factor degrees. -/
theorem tensorProduct_degree (G : WeightedGraph V) (H : WeightedGraph W)
    (p : V × W) :
    (tensorProduct G H).degree p = G.degree p.1 * H.degree p.2 := by
  obtain ⟨v, w⟩ := p
  simp only [degree, tensorProduct_adj, Fintype.sum_prod_type]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun v' _ => ?_)
  rw [Finset.mul_sum]

/-- The tensor product of `dG`-regular and `dH`-regular graphs is
`(dG * dH)`-regular. -/
theorem tensorProduct_isRegular (G : WeightedGraph V) (H : WeightedGraph W)
    {dG dH : ℂ} (hG : G.isRegular dG) (hH : H.isRegular dH) :
    (tensorProduct G H).isRegular (dG * dH) := by
  intro p
  rw [tensorProduct_degree, hG p.1, hH p.2]

/-- Degree of a vertex in the strong product is `dG + dH + dG·dH`. -/
theorem strongProduct_degree (G : WeightedGraph V) (H : WeightedGraph W)
    (p : V × W) :
    (strongProduct G H).degree p =
      G.degree p.1 + H.degree p.2 + G.degree p.1 * H.degree p.2 := by
  have hsum : (strongProduct G H).degree p
      = (cartesianProduct G H).degree p + (tensorProduct G H).degree p := by
    simp only [degree, strongProduct_adj_eq_cartesian_add_tensor, Matrix.add_apply,
      Finset.sum_add_distrib]
  rw [hsum, cartesianProduct_degree, tensorProduct_degree]

/-- The strong product of `dG`-regular and `dH`-regular graphs is
`(dG + dH + dG·dH)`-regular. -/
theorem strongProduct_isRegular (G : WeightedGraph V) (H : WeightedGraph W)
    {dG dH : ℂ} (hG : G.isRegular dG) (hH : H.isRegular dH) :
    (strongProduct G H).isRegular (dG + dH + dG * dH) := by
  intro p
  rw [strongProduct_degree, hG p.1, hH p.2]

end WeightedGraph

end Graphplay
