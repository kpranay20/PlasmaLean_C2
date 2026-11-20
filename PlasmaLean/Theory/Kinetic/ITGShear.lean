/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.ITGBoozer

/-!
# Magnetic shear forces bad curvature along an extended flux tube

Note N-48 §9, question Q-36. In field-line coordinates on the vacuum Boozer model
(`Theory/Kinetic/ITGBoozer`), the radial `∇B` drift frequency of the ITG available energy is
`ω_α ∝ ∂_ψ B|_{α,φ} = ∂_ψ B + ι′ φ ∂_θ B` (`dPsiLogB`; physically `v_∇·∇α`, `ITGDriftChart`). The
shear term grows linearly along the line. This file shows, quantitatively, that a **lower bound
on the shear** `|ι′| ≥ s₀ > 0` forces points of arbitrarily bad curvature: wherever `∂_θ B` reaches
`±c` beyond the tube length `L = (M_ψ + K B_max)/(s₀ c)`, there is a point with
`∂_ψ ln B|_{α,φ} < −K`.

## Why this matters

* The source of the ITG available energy (Mackenbach et al. 2025, eq. 2.35) states a stability
  condition `min v_∇·∇α / B₀ ≥ −|∂_ψ ln T|`; `itg_stability_condition_fails` shows that on a
  sheared tube with `∂_θ B ≠ 0` it fails once the tube is longer than an explicit length: the
  condition can only hold on a **finite** flux tube, and the shear sets how long.
* The stability windows of `ITGStabilityWindows` need good curvature (`η_B < 0`); with a peaked
  density, `∂_ψ ln B|_α < 0` is bad curvature (`η_B > 0`).
* **Input from the certificate.** At torus C of the Dommaschk candidate the certified KAM twist
  `tauC = 14.1623` gives `|dι/dΦ| ≥ 14.16/2π ≈ 2.254` (N-48 §8; the identification of the twist
  with `2π ι′` is numerical, and `ι′` here is per unit toroidal flux `Φ = 2πψ`, so
  `|dι/dψ| ≥ 14.16`). That is a value of `s₀`; `M_ψ`, `c`, `B_max` along the line are not yet
  certified (they need the chart, Q-35 (d)).

## Results

* `shear_term_dominates`: the real-variable core.
* `exists_bad_curvature`: two points beyond `L` where `∂_θ B ≥ c` and `∂_θ B ≤ −c` give one
  where `∂_ψ B + ι′ φ ∂_θ B < −K`, whatever the sign of `ι′`.
* `boozer_bad_curvature`: the same for `dPsiLogB` on a `BoozerField`, with `∂_ψ ln B < −K`.
* `itg_stability_condition_fails`: the source's condition (2.35) fails at that point.
* Sanity: `no_shear_no_growth` (with `ι′ = 0` the drift is bounded by `M_ψ` along the line).

**Not covered.** The existence of the two points (an ergodicity/equidistribution statement for
the line `θ = α + ιφ`, `ι` irrational, and `∂_θ B` of mean zero over `θ`); certified values of
`M_ψ`, `c`, `B_max`; the Whitney-family theorem behind `|ι′| ≥ s₀`.
-/

public section
noncomputable section

namespace PlasmaLean.Kinetic.ITGAE

open PlasmaLean.Kinetic.Boozer

/-- **The shear term dominates.** If `|∂_ψ B| ≤ M`, `φ > 0`, `ι′ ∂_θ B ≤ −s₀ c` (with
`s₀, c > 0`, `K ≥ 0`) and `φ > (M + K)/(s₀ c)`, then `∂_ψ B + ι′ φ ∂_θ B < −K`. -/
theorem shear_term_dominates {Bψ Bθ dι φ M K s₀ c : ℝ} (hM : |Bψ| ≤ M) (hK : 0 ≤ K)
    (hs : 0 < s₀) (hc : 0 < c) (hsign : dι * Bθ ≤ -(s₀ * c)) (hφ : (M + K) / (s₀ * c) < φ) :
    Bψ + dι * φ * Bθ < -K := by
  have hsc : 0 < s₀ * c := mul_pos hs hc
  have hφ0 : M + K < φ * (s₀ * c) := by rwa [div_lt_iff₀ hsc] at hφ
  have hφpos : 0 < φ := by
    by_contra h
    push Not at h
    have h1 : 0 ≤ M := le_trans (abs_nonneg _) hM
    have := mul_nonpos_of_nonpos_of_nonneg h hsc.le
    linarith
  have h2 : dι * φ * Bθ ≤ -(φ * (s₀ * c)) := by
    have := mul_le_mul_of_nonneg_left hsign hφpos.le
    nlinarith
  linarith [le_abs_self Bψ, neg_abs_le Bψ]

/-- **Bad curvature exists, whatever the sign of the shear.** If `|ι′| ≥ s₀ > 0`, `|∂_ψ B| ≤ M`
at two points `φ₁, φ₂ > (M + K)/(s₀ c)` where `∂_θ B ≥ c` and `∂_θ B ≤ −c` respectively, then at one
of them `∂_ψ B + ι′ φ ∂_θ B < −K`. -/
theorem exists_bad_curvature {dι s₀ c M K φ₁ φ₂ Bψ₁ Bψ₂ Bθ₁ Bθ₂ : ℝ} (hK : 0 ≤ K) (hs : 0 < s₀)
    (hι : s₀ ≤ |dι|) (hc : 0 < c) (hM₁ : |Bψ₁| ≤ M) (hM₂ : |Bψ₂| ≤ M)
    (hφ₁ : (M + K) / (s₀ * c) < φ₁) (hφ₂ : (M + K) / (s₀ * c) < φ₂)
    (h₁ : c ≤ Bθ₁) (h₂ : Bθ₂ ≤ -c) :
    Bψ₁ + dι * φ₁ * Bθ₁ < -K ∨ Bψ₂ + dι * φ₂ * Bθ₂ < -K := by
  rcases le_or_gt 0 dι with hd | hd
  · -- `ι′ > 0` (as `|ι′| ≥ s₀ > 0`): use the point with `∂_θ B ≤ −c`
    right
    have hd' : s₀ ≤ dι := by rwa [abs_of_nonneg hd] at hι
    refine shear_term_dominates hM₂ hK hs hc ?_ hφ₂
    nlinarith
  · left
    have hd' : s₀ ≤ -dι := by rwa [abs_of_neg hd] at hι
    refine shear_term_dominates hM₁ hK hs hc ?_ hφ₁
    nlinarith

/-- **Bad curvature on the Boozer model.** With `0 < B ≤ B_max` and the hypotheses of
`exists_bad_curvature` at two points of the field line `α` on the surface `ψ`, one of them has
`∂_ψ ln B|_{α,φ} < −K`. -/
theorem boozer_bad_curvature (F : BoozerField) (dι : ℝ → ℝ) {ψ α s₀ c M K Bmax φ₁ φ₂ : ℝ}
    (hs : 0 < s₀) (hι : s₀ ≤ |dι ψ|) (hc : 0 < c) (hK : 0 ≤ K) (hBmax : 0 < Bmax)
    (hB₁ : 0 < F.B ψ (thetaOf F ψ α φ₁) φ₁) (hB₁' : F.B ψ (thetaOf F ψ α φ₁) φ₁ ≤ Bmax)
    (hB₂ : 0 < F.B ψ (thetaOf F ψ α φ₂) φ₂) (hB₂' : F.B ψ (thetaOf F ψ α φ₂) φ₂ ≤ Bmax)
    (hM₁ : |F.Bψ ψ (thetaOf F ψ α φ₁) φ₁| ≤ M) (hM₂ : |F.Bψ ψ (thetaOf F ψ α φ₂) φ₂| ≤ M)
    (hφ₁ : (M + K * Bmax) / (s₀ * c) < φ₁) (hφ₂ : (M + K * Bmax) / (s₀ * c) < φ₂)
    (h₁ : c ≤ F.Bθ ψ (thetaOf F ψ α φ₁) φ₁) (h₂ : F.Bθ ψ (thetaOf F ψ α φ₂) φ₂ ≤ -c) :
    dPsiLogB F dι ψ α φ₁ < -K ∨ dPsiLogB F dι ψ α φ₂ < -K := by
  have key := exists_bad_curvature (mul_nonneg hK hBmax.le) hs hι hc hM₁ hM₂ hφ₁ hφ₂ h₁ h₂
  have conv : ∀ {B N : ℝ}, 0 < B → B ≤ Bmax → N < -(K * Bmax) → N / B < -K := by
    intro B N hB hBle hN
    rw [div_lt_iff₀ hB]
    have : K * B ≤ K * Bmax := mul_le_mul_of_nonneg_left hBle hK
    linarith
  rcases key with h | h
  · exact Or.inl (conv hB₁ hB₁' h)
  · exact Or.inr (conv hB₂ hB₂' h)

/-- **The source's stability condition fails on a long sheared tube.** Mackenbach et al. (2025),
eq. 2.35, needs `∂_ψ ln B|_{α,φ} ≥ −|∂_ψ ln T|` (in the `ln B` form) along the tube. Under the
hypotheses of `boozer_bad_curvature` with `K = |∂_ψ ln T|`, it fails at one of the two points. -/
theorem itg_stability_condition_fails (F : BoozerField) (dι : ℝ → ℝ)
    {ψ α s₀ c M Bmax φ₁ φ₂ dlnT : ℝ}
    (hs : 0 < s₀) (hι : s₀ ≤ |dι ψ|) (hc : 0 < c) (hBmax : 0 < Bmax)
    (hB₁ : 0 < F.B ψ (thetaOf F ψ α φ₁) φ₁) (hB₁' : F.B ψ (thetaOf F ψ α φ₁) φ₁ ≤ Bmax)
    (hB₂ : 0 < F.B ψ (thetaOf F ψ α φ₂) φ₂) (hB₂' : F.B ψ (thetaOf F ψ α φ₂) φ₂ ≤ Bmax)
    (hM₁ : |F.Bψ ψ (thetaOf F ψ α φ₁) φ₁| ≤ M) (hM₂ : |F.Bψ ψ (thetaOf F ψ α φ₂) φ₂| ≤ M)
    (hφ₁ : (M + |dlnT| * Bmax) / (s₀ * c) < φ₁) (hφ₂ : (M + |dlnT| * Bmax) / (s₀ * c) < φ₂)
    (h₁ : c ≤ F.Bθ ψ (thetaOf F ψ α φ₁) φ₁) (h₂ : F.Bθ ψ (thetaOf F ψ α φ₂) φ₂ ≤ -c) :
    ¬ (-|dlnT| ≤ dPsiLogB F dι ψ α φ₁ ∧ -|dlnT| ≤ dPsiLogB F dι ψ α φ₂) := by
  rintro ⟨g₁, g₂⟩
  rcases boozer_bad_curvature F dι hs hι hc (abs_nonneg dlnT) hBmax hB₁ hB₁' hB₂ hB₂' hM₁ hM₂
    hφ₁ hφ₂ h₁ h₂ with h | h <;> linarith

/-- **Sanity: no shear, no growth.** With `ι′ = 0` the radial-derivative term is bounded by `M`
along the whole line. -/
theorem no_shear_no_growth {Bψ Bθ φ M : ℝ} (hM : |Bψ| ≤ M) : |Bψ + 0 * φ * Bθ| ≤ M := by
  simpa using hM

end PlasmaLean.Kinetic.ITGAE
