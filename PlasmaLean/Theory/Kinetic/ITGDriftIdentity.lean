/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.BiotSavart

/-!
# The `∇B` drift in vacuum Boozer coordinates

Note N-47 §4, question Q-35 (c′). The ITG available-energy drifts of `Theory/Kinetic/ITGBoozer`
are partial derivatives of `ln |B|` in field-line coordinates `(ψ, α = θ − ιφ, φ)`. The source
(Mackenbach et al. 2025, eq. 2.10) identifies them with the physical `∇B` drift:
`v_∇·∇α = ∂_ψ B|_{α,ℓ}`, `v_∇·∇ψ = −∂_α B|_{ψ,ℓ}` (with `v_∇ = b × ∇ ln B`). This file proves that
identification in vacuum Boozer coordinates with `ℓ ↦ φ`, as linear algebra at one point.

## Statement (`boozer_drift_identity`)

Let `e₁, e₂, e₃` be the coordinate vectors `∂x/∂ψ, ∂x/∂θ, ∂x/∂φ` of a chart at a point, with
Jacobian `J = e₁ · (e₂ × e₃) ≠ 0`. Suppose

* the field is in covariant vacuum Boozer form there: `B·e₁ = 0`, `B·e₂ = 0`, `B·e₃ = G`, and
  `G = J |B|²` (`Contract.BoozerChart.G_eq`);
* `v` is a vector with `v·eᵢ = bᵢ` (for `v = ∇|B|`, the chain rule: `bᵢ` are the chart partial
  derivatives of `|B|`);
* `A` is a vector with `A·eᵢ = cᵢ` (for `A = ∇f`, `cᵢ` are the chart partial derivatives of a
  coordinate function `f`).

Then `(B × v)·A = |B|² (b₁ c₂ − b₂ c₁)`. No inverse chart is needed: the hypotheses determine `v`
and `A` (Cramer, `smul_eq_dual`).

Corollaries (`drift_alpha`, `drift_psi`): with `α = θ − ιφ`, `∇α·e = (−ι′φ, 1, −ι)` and
`∇ψ·e = (1, 0, 0)`, so `(b × ∇B)·∇α / |B| = ∂_ψ B + ι′φ ∂_θ B` and `(b × ∇B)·∇ψ / |B| = −∂_θ B`,
exactly the inputs `dPsiLogB`, `dAlphaLogB` of `ITGBoozer` (times `|B|`), with no metric factor.
-/

public section
noncomputable section

namespace PlasmaLean.Kinetic.ITGAE

open PlasmaLean.Fields Matrix WithLp
open scoped RealInnerProductSpace

/-- Components of the cross product. -/
theorem cross_apply' (u v : Space) :
    cross u v 0 = u 1 * v 2 - u 2 * v 1 ∧ cross u v 1 = u 2 * v 0 - u 0 * v 2 ∧
      cross u v 2 = u 0 * v 1 - u 1 * v 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [cross, crossProduct]

/-- The inner product on `Space` in components. -/
theorem inner_three (u v : Space) : ⟪u, v⟫ = u 0 * v 0 + u 1 * v 1 + u 2 * v 2 := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three]
  ring

/-- **Cramer expansion.** `J v = (v·e₁) e₂×e₃ + (v·e₂) e₃×e₁ + (v·e₃) e₁×e₂`, `J = e₁·(e₂×e₃)`. -/
theorem smul_eq_dual (e₁ e₂ e₃ v : Space) :
    ⟪e₁, cross e₂ e₃⟫ • v =
      ⟪v, e₁⟫ • cross e₂ e₃ + ⟪v, e₂⟫ • cross e₃ e₁ + ⟪v, e₃⟫ • cross e₁ e₂ := by
  ext i
  fin_cases i <;>
  · simp only [inner_three, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, (cross_apply' _ _).1,
      (cross_apply' _ _).2.1, (cross_apply' _ _).2.2, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    ring

/-- The triple product of the dual-type vectors: with `X₁ = e₂×e₃`, `X₂ = e₃×e₁`, `X₃ = e₁×e₂`,
`(G X₃ × Σ bᵢ Xᵢ)·Σ cⱼ Xⱼ = G J² (b₁ c₂ − b₂ c₁)`. -/
theorem triple_dual (e₁ e₂ e₃ : Space) (G b₁ b₂ b₃ c₁ c₂ c₃ : ℝ) :
    ⟪cross (G • cross e₁ e₂) (b₁ • cross e₂ e₃ + b₂ • cross e₃ e₁ + b₃ • cross e₁ e₂),
        c₁ • cross e₂ e₃ + c₂ • cross e₃ e₁ + c₃ • cross e₁ e₂⟫ =
      G * ⟪e₁, cross e₂ e₃⟫ ^ 2 * (b₁ * c₂ - b₂ * c₁) := by
  simp only [inner_three, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, (cross_apply' _ _).1,
    (cross_apply' _ _).2.1, (cross_apply' _ _).2.2]
  ring

/-- Scaling all three arguments of `(B × v)·A` by `J` multiplies it by `J³`. -/
theorem triple_smul (J : ℝ) (B v A : Space) :
    ⟪cross (J • B) (J • v), J • A⟫ = J ^ 3 * ⟪cross B v, A⟫ := by
  simp only [inner_three, PiLp.smul_apply, smul_eq_mul, (cross_apply' _ _).1,
    (cross_apply' _ _).2.1, (cross_apply' _ _).2.2]
  ring

/-- **The `∇B` drift in vacuum Boozer coordinates.** With `B·e₁ = B·e₂ = 0`, `B·e₃ = G`,
`G = J|B|²`, `v·eᵢ = bᵢ` and `A·eᵢ = cᵢ`: `(B × v)·A = |B|² (b₁ c₂ − b₂ c₁)`. -/
theorem boozer_drift_identity {e₁ e₂ e₃ B v A : Space} {G b₁ b₂ b₃ c₁ c₂ c₃ : ℝ}
    (hJ : ⟪e₁, cross e₂ e₃⟫ ≠ 0)
    (hB₁ : ⟪B, e₁⟫ = 0) (hB₂ : ⟪B, e₂⟫ = 0) (hB₃ : ⟪B, e₃⟫ = G)
    (hG : G = ⟪e₁, cross e₂ e₃⟫ * ‖B‖ ^ 2)
    (hv₁ : ⟪v, e₁⟫ = b₁) (hv₂ : ⟪v, e₂⟫ = b₂) (hv₃ : ⟪v, e₃⟫ = b₃)
    (hA₁ : ⟪A, e₁⟫ = c₁) (hA₂ : ⟪A, e₂⟫ = c₂) (hA₃ : ⟪A, e₃⟫ = c₃) :
    ⟪cross B v, A⟫ = ‖B‖ ^ 2 * (b₁ * c₂ - b₂ * c₁) := by
  set J := ⟪e₁, cross e₂ e₃⟫ with hJdef
  have eB := smul_eq_dual e₁ e₂ e₃ B
  have ev := smul_eq_dual e₁ e₂ e₃ v
  have eA := smul_eq_dual e₁ e₂ e₃ A
  rw [hB₁, hB₂, hB₃, zero_smul, zero_smul, zero_add, zero_add] at eB
  rw [hv₁, hv₂, hv₃] at ev
  rw [hA₁, hA₂, hA₃] at eA
  have key : J ^ 3 * ⟪cross B v, A⟫ = J ^ 3 * (‖B‖ ^ 2 * (b₁ * c₂ - b₂ * c₁)) := by
    rw [← triple_smul, eB, ev, eA, triple_dual, ← hJdef, hG]
    ring
  exact mul_left_cancel₀ (pow_ne_zero 3 hJ) key

/-- **`v_∇·∇α = ∂_ψ B + ι′φ ∂_θ B`** (times `|B|`): with `∇α·e = (−ι′φ, 1, −ι)`,
`(B × ∇B)·∇α = |B|² (∂_ψ B + ι′φ ∂_θ B)`. -/
theorem drift_alpha {e₁ e₂ e₃ B v A : Space} {G Bψ Bθ Bφ ι dι φ : ℝ}
    (hJ : ⟪e₁, cross e₂ e₃⟫ ≠ 0)
    (hB₁ : ⟪B, e₁⟫ = 0) (hB₂ : ⟪B, e₂⟫ = 0) (hB₃ : ⟪B, e₃⟫ = G)
    (hG : G = ⟪e₁, cross e₂ e₃⟫ * ‖B‖ ^ 2)
    (hv₁ : ⟪v, e₁⟫ = Bψ) (hv₂ : ⟪v, e₂⟫ = Bθ) (hv₃ : ⟪v, e₃⟫ = Bφ)
    (hA₁ : ⟪A, e₁⟫ = -(dι * φ)) (hA₂ : ⟪A, e₂⟫ = 1) (hA₃ : ⟪A, e₃⟫ = -ι) :
    ⟪cross B v, A⟫ = ‖B‖ ^ 2 * (Bψ + dι * φ * Bθ) := by
  rw [boozer_drift_identity hJ hB₁ hB₂ hB₃ hG hv₁ hv₂ hv₃ hA₁ hA₂ hA₃]
  ring

/-- **`v_∇·∇ψ = −∂_θ B`** (times `|B|`): with `∇ψ·e = (1, 0, 0)`,
`(B × ∇B)·∇ψ = −|B|² ∂_θ B`. -/
theorem drift_psi {e₁ e₂ e₃ B v A : Space} {G Bψ Bθ Bφ : ℝ}
    (hJ : ⟪e₁, cross e₂ e₃⟫ ≠ 0)
    (hB₁ : ⟪B, e₁⟫ = 0) (hB₂ : ⟪B, e₂⟫ = 0) (hB₃ : ⟪B, e₃⟫ = G)
    (hG : G = ⟪e₁, cross e₂ e₃⟫ * ‖B‖ ^ 2)
    (hv₁ : ⟪v, e₁⟫ = Bψ) (hv₂ : ⟪v, e₂⟫ = Bθ) (hv₃ : ⟪v, e₃⟫ = Bφ)
    (hA₁ : ⟪A, e₁⟫ = 1) (hA₂ : ⟪A, e₂⟫ = 0) (hA₃ : ⟪A, e₃⟫ = 0) :
    ⟪cross B v, A⟫ = -(‖B‖ ^ 2 * Bθ) := by
  rw [boozer_drift_identity hJ hB₁ hB₂ hB₃ hG hv₁ hv₂ hv₃ hA₁ hA₂ hA₃]
  ring

end PlasmaLean.Kinetic.ITGAE
