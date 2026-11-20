/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.ITGDriftIdentity
public import PlasmaLean.Theory.Contract.BoozerModel

/-!
# The ITG drift identity on a Boozer chart of a physical field

Note N-47 §4, question Q-35 (c′). Specializes `boozer_drift_identity` to a
`Contract.BoozerChart`: at a chart point `p`, with `eᵢ` the chart's coordinate vectors, the
covariant vacuum Boozer form (`cov_psi`, `cov_theta`, `cov_phi`) and `G = J |B|²`
(`BoozerChart.G_eq`) come from the chart itself. For a vector `v` with `v·eᵢ = bᵢ` (the chain
rule for `∇|B|`, supplied) and `A` with `A·eᵢ = cᵢ` (the gradient of a coordinate function,
supplied), `(B × v)·A = |B|² (b₁ c₂ − b₂ c₁)` (`chart_drift_identity`), so

* `(B × ∇|B|)·∇α = |B|² (∂_ψ B + ι′φ ∂_θ B)` (`chart_drift_alpha`),
* `(B × ∇|B|)·∇ψ = −|B|² ∂_θ B` (`chart_drift_psi`),

i.e. `v_∇·∇α = ∂_ψ B|_{α,φ}` and `v_∇·∇ψ = −∂_α B|_{ψ,φ}` with the Boozer `φ` along the line,
the source's eq. 2.10 with no metric factor. This closes the hand calculation of
`Theory/Kinetic/ITGBoozer`.

**Not covered.** Deriving `v·eᵢ = bᵢ` from `modB` and differentiability of `|B|` (a chain-rule
lemma), and `A·eᵢ = cᵢ` from a differentiable inverse chart.
-/

public section
noncomputable section

namespace PlasmaLean.Kinetic.ITGAE

open PlasmaLean.Fields PlasmaLean.Contract PlasmaLean.Kinetic.Boozer Matrix WithLp
open scoped RealInnerProductSpace

/-- The chart Jacobian is `e₁ · (e₂ × e₃)` in the inner-product form. -/
theorem tripleFlux_eq_inner (u v w : Space) : tripleFlux u v w = ⟪u, cross v w⟫ := by
  rw [inner_three]
  simp only [tripleFlux, dotProduct, Fin.sum_univ_three, (cross_apply' _ _).1,
    (cross_apply' _ _).2.1, (cross_apply' _ _).2.2]
  simp [crossProduct]

/-- **The drift identity on a Boozer chart.** -/
theorem chart_drift_identity {B : Space → Space} {Ω : Set Space} {c : ℝ} {F : BoozerField}
    (X : BoozerChart B Ω c F) {p : ℝ × ℝ × ℝ} (hp : p ∈ chartRegion c) {v A : Space}
    {b₁ b₂ b₃ c₁ c₂ c₃ : ℝ}
    (hv₁ : ⟪v, chartPsi X.x p⟫ = b₁) (hv₂ : ⟪v, chartTheta X.x p⟫ = b₂)
    (hv₃ : ⟪v, chartPhi X.x p⟫ = b₃)
    (hA₁ : ⟪A, chartPsi X.x p⟫ = c₁) (hA₂ : ⟪A, chartTheta X.x p⟫ = c₂)
    (hA₃ : ⟪A, chartPhi X.x p⟫ = c₃) :
    ⟪cross (B (X.x p)) v, A⟫ = ‖B (X.x p)‖ ^ 2 * (b₁ * c₂ - b₂ * c₁) := by
  have hJ : ⟪chartPsi X.x p, cross (chartTheta X.x p) (chartPhi X.x p)⟫ ≠ 0 := by
    rw [← tripleFlux_eq_inner]; exact X.jac_ne p hp
  have hG : F.G = ⟪chartPsi X.x p, cross (chartTheta X.x p) (chartPhi X.x p)⟫ *
      ‖B (X.x p)‖ ^ 2 := by
    rw [← tripleFlux_eq_inner]; exact X.G_eq hp
  exact boozer_drift_identity hJ (X.cov_psi p hp) (X.cov_theta p hp) (X.cov_phi p hp) hG
    hv₁ hv₂ hv₃ hA₁ hA₂ hA₃

/-- **`v_∇·∇α` on a Boozer chart**: `(B × ∇|B|)·∇α = |B|² (∂_ψ B + ι′φ ∂_θ B)` for `α = θ − ιφ`. -/
theorem chart_drift_alpha {B : Space → Space} {Ω : Set Space} {c : ℝ} {F : BoozerField}
    (X : BoozerChart B Ω c F) {p : ℝ × ℝ × ℝ} (hp : p ∈ chartRegion c) {v A : Space}
    {dι : ℝ}
    (hv₁ : ⟪v, chartPsi X.x p⟫ = F.Bψ p.1 p.2.1 p.2.2)
    (hv₂ : ⟪v, chartTheta X.x p⟫ = F.Bθ p.1 p.2.1 p.2.2)
    (hv₃ : ⟪v, chartPhi X.x p⟫ = F.Bφ p.1 p.2.1 p.2.2)
    (hA₁ : ⟪A, chartPsi X.x p⟫ = -(dι * p.2.2)) (hA₂ : ⟪A, chartTheta X.x p⟫ = 1)
    (hA₃ : ⟪A, chartPhi X.x p⟫ = -F.ι p.1) :
    ⟪cross (B (X.x p)) v, A⟫ =
      ‖B (X.x p)‖ ^ 2 * (F.Bψ p.1 p.2.1 p.2.2 + dι * p.2.2 * F.Bθ p.1 p.2.1 p.2.2) := by
  rw [chart_drift_identity X hp hv₁ hv₂ hv₃ hA₁ hA₂ hA₃]
  ring

/-- **`v_∇·∇ψ` on a Boozer chart**: `(B × ∇|B|)·∇ψ = −|B|² ∂_θ B`. -/
theorem chart_drift_psi {B : Space → Space} {Ω : Set Space} {c : ℝ} {F : BoozerField}
    (X : BoozerChart B Ω c F) {p : ℝ × ℝ × ℝ} (hp : p ∈ chartRegion c) {v A : Space}
    (hv₁ : ⟪v, chartPsi X.x p⟫ = F.Bψ p.1 p.2.1 p.2.2)
    (hv₂ : ⟪v, chartTheta X.x p⟫ = F.Bθ p.1 p.2.1 p.2.2)
    (hv₃ : ⟪v, chartPhi X.x p⟫ = F.Bφ p.1 p.2.1 p.2.2)
    (hA₁ : ⟪A, chartPsi X.x p⟫ = 1) (hA₂ : ⟪A, chartTheta X.x p⟫ = 0)
    (hA₃ : ⟪A, chartPhi X.x p⟫ = 0) :
    ⟪cross (B (X.x p)) v, A⟫ = -(‖B (X.x p)‖ ^ 2 * F.Bθ p.1 p.2.1 p.2.2) := by
  rw [chart_drift_identity X hp hv₁ hv₂ hv₃ hA₁ hA₂ hA₃]
  ring

end PlasmaLean.Kinetic.ITGAE
