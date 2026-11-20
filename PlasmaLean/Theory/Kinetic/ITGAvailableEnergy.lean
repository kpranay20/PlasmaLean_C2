/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Available energy of the curvature-driven ITG instability: the algebra

Note N-47 (`notes/theory/itg-available-energy.md`), question Q-35; layer 2 of the turbulence
programme (N-45 §4).

## Source and model (supplied)

R. Mackenbach, P. Helander, M. Landreman, S. Brunner, J. Proll, *On the curvature-driven
ion-temperature-gradient instability and its available energy*, J. Plasma Phys. (2025). Flux
tube `B = ∇ψ × ∇α`, collisionless, electrostatic, adiabatic electrons, parallel dynamics
neglected, density profile held fixed, local Maxwellian, correlation domain the unit disk in
`(ψ − ψ₀)/Δψ`, `(α − α₀)/Δα`. At each point `(ℓ, μ, v∥)` of the flux tube (their eqs. 2.8, 2.21):

* `ω_α = μ B₀ ∂_ψ ln B|_{α,ℓ}`, `ω_ψ = −μ B₀ ∂_α ln B|_{ψ,ℓ}` (the `∇B` drifts across and along
  the surface: **the geometry**), `ω*^T = T₀[d ln n/dψ + d ln T/dψ (ε/T₀ − 3/2)]` (the drive),
  `κ_α(ℓ)`, `κ_ψ(ℓ)` the ground-state parameters;
* `a = Δψ (ω_α + κ_α)`, `b = Δα (ω_ψ − κ_ψ)`, `c = Δψ (ω_α − ω*^T)`, `d = Δα ω_ψ`;
* the available energy `A = C ∫ (f_M/T₀) [√(a² + b²) √(c² + d²) − a c − b d]` with a positive
  normalization `C` (the source's `π²ΔψΔα/(4m)`; its Jacobian constant is unchecked, N-47 §2, so
  `C > 0` is kept general);
* the ground state `G = √((c² + d²)/(a² + b²))` with constraints `∫ w a G = ∫ w c`,
  `∫ w b G = ∫ w d` at each `ℓ` (their eq. 2.17, rewritten).

The formula is the source's evaluation of `A = E[f] − E[ground state]`; its derivation (the
variational problem and the uniqueness of `κ`) is **not** formalized here: `aeFormula` is that
formula, a supplied model law.

## Results

* `aeIntegrand_nonneg` (Cauchy–Schwarz via the Lagrange identity), `aeFormula_nonneg`.
* `aeIntegrand_eq_zero_iff`: the integrand vanishes **iff** `a d = b c` **and** `a c + b d ≥ 0`
  (the vectors are parallel and point the same way). The source states only `a d = b c`
  (its eq. 2.23); `aeIntegrand_pos_of_antiparallel` shows the sign condition is needed.
* `itgIntegrand_eq_zero_iff`: in physical variables, for `Δψ Δα ≠ 0`: vanishing iff
  `κ_ψ (ω* − ω_α) = ω_ψ (ω* + κ_α)` (eq. 2.23) and
  `Δψ² (ω_α + κ_α)(ω_α − ω*) + Δα² (ω_ψ − κ_ψ) ω_ψ ≥ 0`.
* `aeIntegrand_isodynamic`: with `b = d = 0` (no radial drift and `κ_ψ = 0`), the integrand is
  `2 (−a c)₊` (eq. 2.28).
* `aeIntegrand_smul`: scaling all of `a, b, c, d` by `t` scales the integrand by `t²` (with the
  prefactor `ΔψΔα`, `A → t⁴ A`).
* **Sanity, accepted fixture:** `itg_ae_zero_of_no_temperature_gradient`: with an
  energy-independent `ω*` (`η = 0`), the choice `κ_α = −ω*`, `κ_ψ = 0` satisfies the ground-state
  constraints (`groundState_constraints_flat`) and gives `A = 0` in **every** geometry: a density
  gradient alone releases no energy in this model.
* **Sanity, rejected fixture:** `aeIntegrand_pos_of_antiparallel`.

**Not covered.** The variational derivation and uniqueness of the ground state; the stability
windows `0 ≤ η ≤ 2/3`, `η ≥ η_B` (next step); evaluation on a certified field (the drift
quantities from the Boozer model, Q-35 (c)).
-/

public section
noncomputable section

namespace PlasmaLean.Kinetic.ITGAE

open Real MeasureTheory

/-! ## The integrand -/

/-- The available-energy integrand `√(a² + b²) √(c² + d²) − (a c + b d)`. -/
@[expose] def aeIntegrand (a b c d : ℝ) : ℝ := √(a ^ 2 + b ^ 2) * √(c ^ 2 + d ^ 2) - (a * c + b * d)

/-- The Lagrange identity `(a² + b²)(c² + d²) = (a c + b d)² + (a d − b c)²`. -/
theorem lagrange_identity (a b c d : ℝ) :
    (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) = (a * c + b * d) ^ 2 + (a * d - b * c) ^ 2 := by
  ring

/-- `√(a² + b²) √(c² + d²) = √((a c + b d)² + (a d − b c)²)`. -/
theorem sqrt_mul_sqrt_eq (a b c d : ℝ) :
    √(a ^ 2 + b ^ 2) * √(c ^ 2 + d ^ 2) = √((a * c + b * d) ^ 2 + (a * d - b * c) ^ 2) := by
  rw [← lagrange_identity, Real.sqrt_mul (by positivity)]

/-- **Cauchy–Schwarz in the plane**: `a c + b d ≤ √(a² + b²) √(c² + d²)`. -/
theorem inner_le_sqrt_mul_sqrt (a b c d : ℝ) :
    a * c + b * d ≤ √(a ^ 2 + b ^ 2) * √(c ^ 2 + d ^ 2) := by
  rw [sqrt_mul_sqrt_eq]
  calc a * c + b * d ≤ |a * c + b * d| := le_abs_self _
    _ = √((a * c + b * d) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ √((a * c + b * d) ^ 2 + (a * d - b * c) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (a * d - b * c)])

/-- **The available-energy integrand is nonnegative.** -/
theorem aeIntegrand_nonneg (a b c d : ℝ) : 0 ≤ aeIntegrand a b c d := by
  unfold aeIntegrand
  linarith [inner_le_sqrt_mul_sqrt a b c d]

/-- **Vanishing condition.** The integrand vanishes iff `a d = b c` and `a c + b d ≥ 0`. -/
theorem aeIntegrand_eq_zero_iff (a b c d : ℝ) :
    aeIntegrand a b c d = 0 ↔ a * d = b * c ∧ 0 ≤ a * c + b * d := by
  unfold aeIntegrand
  rw [sqrt_mul_sqrt_eq, sub_eq_zero]
  constructor
  · intro h
    have hnn : 0 ≤ a * c + b * d := h ▸ Real.sqrt_nonneg _
    have hsq := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (a * c + b * d) ^ 2 + (a * d - b * c) ^ 2)
    rw [h] at hsq
    have h0 : (a * d - b * c) ^ 2 = 0 := by linarith
    exact ⟨sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h0), hnn⟩
  · rintro ⟨h1, h2⟩
    rw [sub_eq_zero.2 h1]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
    rw [Real.sqrt_sq h2]

/-- **The sign condition is needed** (rejected fixture for the source's eq. 2.23 alone): if
`(c, d) = −t (a, b)` with `t > 0` and `(a, b) ≠ 0`, then `a d = b c` but the integrand is
`2 t (a² + b²) > 0`. -/
theorem aeIntegrand_pos_of_antiparallel {a b t : ℝ} (ht : 0 < t) (hab : a ≠ 0 ∨ b ≠ 0) :
    a * (-t * b) = b * (-t * a) ∧ 0 < aeIntegrand a b (-t * a) (-t * b) := by
  refine ⟨by ring, ?_⟩
  have hpos : 0 < a ^ 2 + b ^ 2 := by
    rcases hab with h | h
    · have := pow_pos (abs_pos.2 h) 2; rw [sq_abs] at this; positivity
    · have := pow_pos (abs_pos.2 h) 2; rw [sq_abs] at this; positivity
  have e : (-t * a) ^ 2 + (-t * b) ^ 2 = t ^ 2 * (a ^ 2 + b ^ 2) := by ring
  unfold aeIntegrand
  rw [e, Real.sqrt_mul (by positivity), Real.sqrt_sq ht.le]
  have hs := Real.mul_self_sqrt hpos.le
  nlinarith [Real.sqrt_nonneg (a ^ 2 + b ^ 2)]

/-- **Isodynamic reduction** (eq. 2.28): with `b = d = 0`, the integrand is `2 (−a c)₊`. -/
theorem aeIntegrand_isodynamic (a c : ℝ) : aeIntegrand a 0 c 0 = 2 * max 0 (-(a * c)) := by
  unfold aeIntegrand
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, mul_zero,
    Real.sqrt_sq_eq_abs]
  rw [← abs_mul]
  rcases le_total 0 (a * c) with h | h
  · rw [abs_of_nonneg h, max_eq_left (by linarith)]
    ring
  · rw [abs_of_nonpos h, max_eq_right (by linarith)]
    ring

/-- **Scaling.** `aeIntegrand (t a) (t b) (t c) (t d) = t² · aeIntegrand a b c d`. -/
theorem aeIntegrand_smul (t a b c d : ℝ) :
    aeIntegrand (t * a) (t * b) (t * c) (t * d) = t ^ 2 * aeIntegrand a b c d := by
  unfold aeIntegrand
  have e1 : (t * a) ^ 2 + (t * b) ^ 2 = t ^ 2 * (a ^ 2 + b ^ 2) := by ring
  have e2 : (t * c) ^ 2 + (t * d) ^ 2 = t ^ 2 * (c ^ 2 + d ^ 2) := by ring
  rw [e1, e2, Real.sqrt_mul (sq_nonneg t), Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq_eq_abs]
  have : |t| * |t| = t ^ 2 := by rw [← abs_mul, ← sq, abs_sq]
  calc |t| * √(a ^ 2 + b ^ 2) * (|t| * √(c ^ 2 + d ^ 2)) - (t * a * (t * c) + t * b * (t * d))
      = (|t| * |t|) * (√(a ^ 2 + b ^ 2) * √(c ^ 2 + d ^ 2)) - t ^ 2 * (a * c + b * d) := by ring
    _ = t ^ 2 * (√(a ^ 2 + b ^ 2) * √(c ^ 2 + d ^ 2) - (a * c + b * d)) := by rw [this]; ring

/-! ## Physical variables -/

/-- The ITG integrand in physical variables (eq. 2.21): `a = Δψ(ω_α + κ_α)`,
`b = Δα(ω_ψ − κ_ψ)`, `c = Δψ(ω_α − ω*)`, `d = Δα ω_ψ`. -/
@[expose] def itgIntegrand (Δψ Δα ωα ωψ ωs κα κψ : ℝ) : ℝ :=
  aeIntegrand (Δψ * (ωα + κα)) (Δα * (ωψ - κψ)) (Δψ * (ωα - ωs)) (Δα * ωψ)

/-- **Vanishing in physical variables.** For `Δψ Δα ≠ 0`, the ITG integrand vanishes iff
`κ_ψ (ω* − ω_α) = ω_ψ (ω* + κ_α)` (the source's eq. 2.23) and the sign condition
`Δψ² (ω_α + κ_α)(ω_α − ω*) + Δα² (ω_ψ − κ_ψ) ω_ψ ≥ 0` holds. -/
theorem itgIntegrand_eq_zero_iff {Δψ Δα : ℝ} (h : Δψ * Δα ≠ 0) (ωα ωψ ωs κα κψ : ℝ) :
    itgIntegrand Δψ Δα ωα ωψ ωs κα κψ = 0 ↔
      κψ * (ωs - ωα) = ωψ * (ωs + κα) ∧
        0 ≤ Δψ ^ 2 * ((ωα + κα) * (ωα - ωs)) + Δα ^ 2 * ((ωψ - κψ) * ωψ) := by
  unfold itgIntegrand
  rw [aeIntegrand_eq_zero_iff]
  have e1 : Δψ * (ωα + κα) * (Δα * ωψ) - Δα * (ωψ - κψ) * (Δψ * (ωα - ωs)) =
      Δψ * Δα * (ωψ * (ωs + κα) - κψ * (ωs - ωα)) := by ring
  have e2 : Δψ * (ωα + κα) * (Δψ * (ωα - ωs)) + Δα * (ωψ - κψ) * (Δα * ωψ) =
      Δψ ^ 2 * ((ωα + κα) * (ωα - ωs)) + Δα ^ 2 * ((ωψ - κψ) * ωψ) := by ring
  rw [e2, ← sub_eq_zero, e1, mul_eq_zero, sub_eq_zero]
  constructor
  · rintro ⟨h1 | h1, h2⟩
    · exact absurd h1 h
    · exact ⟨h1.symm, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨Or.inr h1.symm, h2⟩

/-! ## The available energy -/

variable {X : Type*} [MeasurableSpace X]

/-- **The available-energy formula** (eq. 2.21, supplied): `C ∫ w · I(a, b, c, d) dμ` over the
flux-tube phase space `X` (points `(ℓ, μ, v∥)`), with weight `w = f_M/T₀` and normalization
`C > 0`. -/
@[expose] def aeFormula (μ : Measure X) (C : ℝ) (w a b c d : X → ℝ) : ℝ :=
  C * ∫ x, w x * aeIntegrand (a x) (b x) (c x) (d x) ∂μ

/-- **The available energy is nonnegative.** -/
theorem aeFormula_nonneg (μ : Measure X) {C : ℝ} (hC : 0 ≤ C) {w : X → ℝ} (hw : ∀ x, 0 ≤ w x)
    (a b c d : X → ℝ) : 0 ≤ aeFormula μ C w a b c d :=
  mul_nonneg hC (integral_nonneg fun x => mul_nonneg (hw x) (aeIntegrand_nonneg _ _ _ _))

/-- If the integrand vanishes everywhere, the available energy is zero. -/
theorem aeFormula_eq_zero_of (μ : Measure X) (C : ℝ) (w a b c d : X → ℝ)
    (h : ∀ x, aeIntegrand (a x) (b x) (c x) (d x) = 0) : aeFormula μ C w a b c d = 0 := by
  simp [aeFormula, h]

/-- The ground state `G = √((c² + d²)/(a² + b²))` (eq. 2.15; `0` where `a = b = 0`). -/
@[expose] def groundState (a b c d : ℝ) : ℝ := √((c ^ 2 + d ^ 2) / (a ^ 2 + b ^ 2))

/-- With `(a, b) = (c, d)` the ground state reproduces the data: `a G = c`, `b G = d`, so the
ground-state constraints `∫ w a G = ∫ w c`, `∫ w b G = ∫ w d` hold. -/
theorem groundState_constraints_flat (a b : ℝ) :
    a * groundState a b a b = a ∧ b * groundState a b a b = b := by
  unfold groundState
  by_cases h : a ^ 2 + b ^ 2 = 0
  · have ha : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
    have hb : b = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
    simp [ha, hb]
  · rw [div_self h, Real.sqrt_one]
    simp

/-- **No temperature gradient, no available energy** (accepted fixture). If `ω*` does not depend
on the energy (`η = 0`, so `ω*` is a function of `ℓ` only, here a single value `ωs` on the tube),
the ground state `κ_α = −ω*`, `κ_ψ = 0` makes `(a, b) = (c, d)`, satisfies the constraints
(`groundState_constraints_flat`), and gives `A = 0` for **every** geometry `ω_α`, `ω_ψ`. -/
theorem itg_ae_zero_of_no_temperature_gradient (μ : Measure X) (C Δψ Δα ωs : ℝ)
    (w ωα ωψ : X → ℝ) :
    aeFormula μ C w (fun x => Δψ * (ωα x + -ωs)) (fun x => Δα * (ωψ x - 0))
      (fun x => Δψ * (ωα x - ωs)) (fun x => Δα * ωψ x) = 0 := by
  apply aeFormula_eq_zero_of
  intro x
  rw [aeIntegrand_eq_zero_iff]
  constructor
  · ring
  · nlinarith [sq_nonneg (Δψ * (ωα x - ωs)), sq_nonneg (Δα * ωψ x)]

end PlasmaLean.Kinetic.ITGAE
