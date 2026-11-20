/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.ITGAvailableEnergy
public import PlasmaLean.Theory.Kinetic.BoozerGuidingCentre
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The ITG available-energy drifts from the vacuum Boozer model

Note N-47 §4, question Q-35 (c). The ITG available energy (`Theory/Kinetic/ITGAvailableEnergy`)
takes the `∇B` drift frequencies `ω_α = μB₀ ∂_ψ ln B|_{α,ℓ}` and `ω_ψ = −μB₀ ∂_α ln B|_{ψ,ℓ}`
as inputs. This file computes them from the vacuum Boozer model `Kinetic.Boozer.BoozerField`
(the model of contract clause C2), so that the available energy becomes a functional of the same
field data that C2 constrains.

## Coordinates

Field-line coordinates `(ψ, α, φ)` with `α = θ − ι(ψ) φ` and the Boozer toroidal angle `φ` as the
coordinate along the field line. Then `θ = α + ι(ψ) φ` and

* `∂_α ln B|_{ψ,φ} = ∂_θ B / B` (`hasDerivAt_logB_alpha`),
* `∂_ψ ln B|_{α,φ} = (∂_ψ B + ι′ φ ∂_θ B) / B` (`hasDerivAt_logB_psi`; the magnetic shear term
  `ι′ φ ∂_θ B` grows along the line).

**Why `φ` is the right parallel coordinate (hand calculation, not yet in Lean).** In vacuum Boozer
form `B = G ∇φ` with Jacobian `J = G/B²`, the dual basis gives
`(∇φ × ∇B)·∇α = (∂_ψ B + ι′φ ∂_θ B)/J` and `(∇φ × ∇B)·∇ψ = −∂_θ B / J`, so
`v_∇·∇α = (b × ∇B)·∇α / B = ∂_ψ B|_{α,φ}` and
`v_∇·∇ψ = −∂_θ B = −∂_α B|_{ψ,φ}` exactly: the source's identity (2.10) holds with `ℓ ↦ φ` and no
metric factor. A Lean proof needs the chart of `Contract.BoozerChart` (follow-up).

## Results

* `hasDerivAt_logB_alpha`, `hasDerivAt_logB_psi`: the drift quantities are the partial
  derivatives of `ln |B|` in field-line coordinates.
* `omegaPsi_eq_zero_of_Btheta`: an isodynamic tube (`∂_θ B = 0` on it) has `ω_ψ = 0`, and then
  the ground state `κ_ψ = 0` gives the isodynamic integrand `2 Δψ² ((κ_α + ω_α)(ω* − ω_α))₊`
  (`boozerIntegrand_isodynamic`).
* `omegaPsi_ne_zero`: wherever `∂_θ B ≠ 0` (for instance in an exactly quasi-axisymmetric field,
  `|B| = B(ψ, θ)`), `ω_ψ ≠ 0`: the local radial drift that the available energy sees is not removed
  by quasisymmetry or omnigeneity (which control its bounce average). C2 does not imply a small
  ITG available energy.
* `paper_condition_not_sufficient`: in physical variables, the source's condition (2.23) holds
  identically on an isodynamic tube, yet the integrand is positive wherever
  `(κ_α + ω_α)(ω* − ω_α) > 0` (the misstatement of the source's §2.3, N-47 §2).

**Not covered.** The drift identity `v_∇·∇α = ∂_ψ B|_{α,φ}` from the chart (above); the
ground-state solve for `κ`; the integration over a certified torus (Q-35 (d)).
-/

public section
noncomputable section

namespace PlasmaLean.Kinetic.ITGAE

open Real PlasmaLean.Kinetic.Boozer

/-- The Boozer poloidal angle on the field line `α` at toroidal angle `φ`: `θ = α + ι(ψ) φ`. -/
@[expose] def thetaOf (F : BoozerField) (ψ α φ : ℝ) : ℝ := α + F.ι ψ * φ

/-- `∂_α ln B` at fixed `(ψ, φ)`: `∂_θ B / B`. -/
@[expose] def dAlphaLogB (F : BoozerField) (ψ α φ : ℝ) : ℝ :=
  F.Bθ ψ (thetaOf F ψ α φ) φ / F.B ψ (thetaOf F ψ α φ) φ

/-- `∂_ψ ln B` at fixed `(α, φ)`: `(∂_ψ B + ι′ φ ∂_θ B) / B`, with `dι = ι′`. -/
@[expose] def dPsiLogB (F : BoozerField) (dι : ℝ → ℝ) (ψ α φ : ℝ) : ℝ :=
  (F.Bψ ψ (thetaOf F ψ α φ) φ + dι ψ * φ * F.Bθ ψ (thetaOf F ψ α φ) φ) /
    F.B ψ (thetaOf F ψ α φ) φ

/-- **`dAlphaLogB` is the derivative of `ln B` along `α`** at fixed `(ψ, φ)`. -/
theorem hasDerivAt_logB_alpha (F : BoozerField) {ψ α φ : ℝ} (hψ : 0 < ψ)
    (hB : 0 < F.B ψ (thetaOf F ψ α φ) φ) :
    HasDerivAt (fun a => Real.log (F.B ψ (thetaOf F ψ a φ) φ)) (dAlphaLogB F ψ α φ) α := by
  have hc : HasDerivAt (fun a : ℝ => (ψ, thetaOf F ψ a φ, φ)) ((0 : ℝ), (1 : ℝ), (0 : ℝ)) α :=
    (hasDerivAt_const α ψ).prodMk
      (((hasDerivAt_id α).add_const (F.ι ψ * φ)).prodMk (hasDerivAt_const α φ))
  have hBd := (F.hasFDerivAt_B (ψ, thetaOf F ψ α φ, φ) hψ).comp_hasDerivAt α hc
  have hl := hBd.log hB.ne'
  simp only [Function.comp_def, gradCLM_apply, mul_zero, mul_one, zero_add, add_zero] at hl
  exact hl

/-- **`dPsiLogB` is the derivative of `ln B` along `ψ`** at fixed `(α, φ)`, given `ι′ = dι`. -/
theorem hasDerivAt_logB_psi (F : BoozerField) (dι : ℝ → ℝ) {ψ α φ : ℝ} (hψ : 0 < ψ)
    (hι : HasDerivAt F.ι (dι ψ) ψ) (hB : 0 < F.B ψ (thetaOf F ψ α φ) φ) :
    HasDerivAt (fun x => Real.log (F.B x (thetaOf F x α φ) φ)) (dPsiLogB F dι ψ α φ) ψ := by
  have hc : HasDerivAt (fun x : ℝ => (x, thetaOf F x α φ, φ))
      ((1 : ℝ), dι ψ * φ, (0 : ℝ)) ψ :=
    (hasDerivAt_id ψ).prodMk
      (((hι.mul_const φ).const_add α).prodMk (hasDerivAt_const ψ φ))
  have hBd := (F.hasFDerivAt_B (ψ, thetaOf F ψ α φ, φ) hψ).comp_hasDerivAt ψ hc
  have hl := hBd.log hB.ne'
  simp only [Function.comp_def, gradCLM_apply, mul_zero, mul_one, add_zero] at hl
  convert hl using 1
  simp only [dPsiLogB]
  ring

/-- The drift frequency across the surface, `ω_α = μ B₀ ∂_ψ ln B|_{α,φ}`. -/
@[expose] def omegaAlpha (F : BoozerField) (dι : ℝ → ℝ) (μ B₀ ψ α φ : ℝ) : ℝ :=
  μ * B₀ * dPsiLogB F dι ψ α φ

/-- The radial drift frequency, `ω_ψ = −μ B₀ ∂_α ln B|_{ψ,φ}`. -/
@[expose] def omegaPsi (F : BoozerField) (μ B₀ ψ α φ : ℝ) : ℝ :=
  -(μ * B₀ * dAlphaLogB F ψ α φ)

/-- **The ITG integrand on the Boozer model** at the phase-space point `(ψ, α, φ; μ)`, with drive
`ω*` and ground-state parameters `κ_α`, `κ_ψ`. -/
@[expose] def boozerIntegrand (F : BoozerField) (dι : ℝ → ℝ) (μ B₀ Δψ Δα ωs κα κψ ψ α φ : ℝ) :
    ℝ :=
  itgIntegrand Δψ Δα (omegaAlpha F dι μ B₀ ψ α φ) (omegaPsi F μ B₀ ψ α φ) ωs κα κψ

/-- **Isodynamic tube.** If `∂_θ B = 0` at the point, the radial drift vanishes. -/
theorem omegaPsi_eq_zero_of_Btheta (F : BoozerField) {μ B₀ ψ α φ : ℝ}
    (h : F.Bθ ψ (thetaOf F ψ α φ) φ = 0) : omegaPsi F μ B₀ ψ α φ = 0 := by
  simp [omegaPsi, dAlphaLogB, h]

/-- **Quasisymmetry does not remove the local radial drift.** If `∂_θ B ≠ 0` and `B ≠ 0` at the
point and `μ B₀ ≠ 0`, then `ω_ψ ≠ 0`. -/
theorem omegaPsi_ne_zero (F : BoozerField) {μ B₀ ψ α φ : ℝ} (hμ : μ * B₀ ≠ 0)
    (hB : F.B ψ (thetaOf F ψ α φ) φ ≠ 0) (h : F.Bθ ψ (thetaOf F ψ α φ) φ ≠ 0) :
    omegaPsi F μ B₀ ψ α φ ≠ 0 := by
  simp only [omegaPsi, dAlphaLogB, neg_ne_zero]
  exact mul_ne_zero hμ (div_ne_zero h hB)

/-- **Isodynamic reduction on the Boozer model.** With `∂_θ B = 0` and `κ_ψ = 0`, the integrand
is `2 Δψ² ((κ_α + ω_α)(ω* − ω_α))₊` (source eq. 2.28). -/
theorem boozerIntegrand_isodynamic (F : BoozerField) (dι : ℝ → ℝ) {μ B₀ Δψ Δα ωs κα ψ α φ : ℝ}
    (h : F.Bθ ψ (thetaOf F ψ α φ) φ = 0) :
    boozerIntegrand F dι μ B₀ Δψ Δα ωs κα 0 ψ α φ =
      2 * max 0 (Δψ ^ 2 * ((κα + omegaAlpha F dι μ B₀ ψ α φ) *
        (ωs - omegaAlpha F dι μ B₀ ψ α φ))) := by
  have h0 := omegaPsi_eq_zero_of_Btheta (μ := μ) (B₀ := B₀) F h
  simp only [boozerIntegrand, itgIntegrand, h0, sub_zero, mul_zero]
  rw [aeIntegrand_isodynamic]
  congr 2
  ring

/-- **The source's condition (2.23) is not sufficient** (N-47 §2). On an isodynamic tube
(`ω_ψ = κ_ψ = 0`) condition (2.23), `κ_ψ (ω* − ω_α) = ω_ψ (ω* + κ_α)`, holds identically, yet the
integrand is positive wherever `Δψ ≠ 0` and `(κ_α + ω_α)(ω* − ω_α) > 0`. -/
theorem paper_condition_not_sufficient {Δψ Δα ωα ωs κα : ℝ} (hΔ : Δψ ≠ 0)
    (hsign : 0 < (κα + ωα) * (ωs - ωα)) :
    (0 : ℝ) * (ωs - ωα) = 0 * (ωs + κα) ∧ 0 < itgIntegrand Δψ Δα ωα 0 ωs κα 0 := by
  refine ⟨by ring, ?_⟩
  simp only [itgIntegrand, sub_zero, mul_zero]
  rw [aeIntegrand_isodynamic]
  have : 0 < -(Δψ * (ωα + κα) * (Δψ * (ωα - ωs))) := by
    have e : -(Δψ * (ωα + κα) * (Δψ * (ωα - ωs))) = Δψ ^ 2 * ((κα + ωα) * (ωs - ωα)) := by ring
    rw [e]
    exact mul_pos (by positivity) hsign
  rw [max_eq_right this.le]
  linarith

end PlasmaLean.Kinetic.ITGAE
