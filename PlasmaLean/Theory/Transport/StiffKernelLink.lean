/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Sanity.Transport
public import PlasmaLean.Theory.Transport.StiffTransport
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Steady kernel solutions satisfy the power balance of the stiff class

Note N-45, question Q-33 (b). The stiff turbulent-transport class
(`Theory/Transport/StiffTransport`) takes the steady power balance `Q ≤ W` as a hypothesis:
the outward heat flow through the surface `ψ` is at most the heating power deposited inside
it. This file derives it, with equality, for a steady profile of the transport kernel
(`Kernel/Transport`).

## Statement

For a profile `f` with `N[f] = 0` on `(0, ψ)` (the kernel operator in expanded form), the
divergence form `(V' D f')' = V' (N[f] − R) = −V' R` (`Sanity.op_divergence_form`) integrates to

`−V'(ψ) D(ψ, f ψ) f'(ψ) = ∫₀^ψ V'(s) R(s, f s) ds`  (`steady_flux_eq_integral`),

once the axis flux `V' D f'` vanishes at `ψ = 0`. It does in both axis conventions of the kernel:
`f'(0) = 0` at a regular axis, `D(0, ·) = 0` at a degenerate one (`axisFlux_eq_zero`). So the heat
flow `Q = −V' D f'` equals the enclosed net source, and with `R ≤ H` (heating minus losses is at
most the heating) `Q ≤ ∫₀^ψ V' H` (`steady_flux_le_heating`): the `balance` hypothesis of
`StiffSteadyProfile` with `W = ∫₀^ψ V' H`.

Units follow the kernel: `R` is a rate of change of temperature, so `Q` and `W` are in
temperature × volume per time; the stiffness `S` of the floor is then in the matching units.

**Not covered.** The chain rule for `ψ ↦ D(ψ, f ψ)` is a hypothesis (as in
`Sanity.op_divergence_form`; the kernel's separate partial derivatives do not imply it); the
existence of a steady solution.
-/

public section
noncomputable section

namespace PlasmaLean.Transport.Stiff

open Set Real MeasureTheory intervalIntegral

/-- **Integrated steady balance.** If `N[f] = 0` on `(0, ψ)`, the divergence form holds there
(chain rule for `D(·, f ·)`), the flux `V' D f'` is continuous on `[0, ψ]` and vanishes at the
axis, and `V' R(·, f ·)` is integrable, then `−V'(ψ) D(ψ, f ψ) f'(ψ) = ∫₀^ψ V' R`. -/
theorem steady_flux_eq_integral (c : RadialCoefficients) {f f' f'' : ℝ → ℝ} {ψ : ℝ}
    (hψ : 0 ≤ ψ)
    (hV : ∀ x ∈ Ioo 0 ψ, HasDerivAt c.Vp (c.dVp x) x)
    (hD : ∀ x ∈ Ioo 0 ψ,
      HasDerivAt (fun s => c.D s (f s)) (c.dD x (f x) + c.dDT x (f x) * f' x) x)
    (hf : ∀ x ∈ Ioo 0 ψ, HasDerivAt f' (f'' x) x)
    (hpos : ∀ x ∈ Ioo 0 ψ, c.Vp x ≠ 0)
    (hsteady : ∀ x ∈ Ioo 0 ψ, c.op x (f x) (f' x) (f'' x) = 0)
    (hcont : ContinuousOn (fun x => c.Vp x * c.D x (f x) * f' x) (Icc 0 ψ))
    (hint : IntervalIntegrable (fun x => c.Vp x * c.R x (f x)) volume 0 ψ)
    (haxis : c.Vp 0 * c.D 0 (f 0) * f' 0 = 0) :
    -(c.Vp ψ * c.D ψ (f ψ) * f' ψ) = ∫ x in (0 : ℝ)..ψ, c.Vp x * c.R x (f x) := by
  have hderiv : ∀ x ∈ Ioo 0 ψ, HasDerivAt (fun s => c.Vp s * c.D s (f s) * f' s)
      (-(c.Vp x * c.R x (f x))) x := by
    intro x hx
    have := Sanity.op_divergence_form c (hV x hx) (hD x hx) (hf x hx) (hpos x hx)
    rw [hsteady x hx, zero_sub, mul_neg] at this
    exact this
  have h := integral_eq_sub_of_hasDerivAt_of_le hψ hcont hderiv hint.neg
  rw [intervalIntegral.integral_neg, haxis, sub_zero] at h
  linarith

/-- **The axis flux vanishes** in both kernel conventions: at a regular axis `f'(0) = 0`, at a
degenerate axis `D(0, ·) = 0` (`TransportLaws.D_axis`). -/
theorem axisFlux_eq_zero (c : RadialCoefficients) [TransportLaws c] {f f' : ℝ → ℝ}
    (hreg : c.axis = .regular → f' 0 = 0) : c.Vp 0 * c.D 0 (f 0) * f' 0 = 0 := by
  cases h : c.axis with
  | regular => rw [hreg h, mul_zero]
  | degenerate => rw [TransportLaws.D_axis h, mul_zero, zero_mul]

/-- **Heat flow is at most the enclosed heating.** If moreover `R(s, f s) ≤ H s` (net source at
most the heating) with `V' ≥ 0` and `V' H` integrable, the heat flow `−V' D f'` through `ψ` is at
most `∫₀^ψ V' H`: the `balance` hypothesis of `StiffSteadyProfile`. -/
theorem steady_flux_le_heating (c : RadialCoefficients) {f f' f'' H : ℝ → ℝ} {ψ : ℝ}
    (hψ : 0 ≤ ψ)
    (hV : ∀ x ∈ Ioo 0 ψ, HasDerivAt c.Vp (c.dVp x) x)
    (hD : ∀ x ∈ Ioo 0 ψ,
      HasDerivAt (fun s => c.D s (f s)) (c.dD x (f x) + c.dDT x (f x) * f' x) x)
    (hf : ∀ x ∈ Ioo 0 ψ, HasDerivAt f' (f'' x) x)
    (hpos : ∀ x ∈ Ioo 0 ψ, c.Vp x ≠ 0)
    (hsteady : ∀ x ∈ Ioo 0 ψ, c.op x (f x) (f' x) (f'' x) = 0)
    (hcont : ContinuousOn (fun x => c.Vp x * c.D x (f x) * f' x) (Icc 0 ψ))
    (hint : IntervalIntegrable (fun x => c.Vp x * c.R x (f x)) volume 0 ψ)
    (hintH : IntervalIntegrable (fun x => c.Vp x * H x) volume 0 ψ)
    (haxis : c.Vp 0 * c.D 0 (f 0) * f' 0 = 0)
    (hVnn : ∀ x ∈ Icc 0 ψ, 0 ≤ c.Vp x) (hRH : ∀ x ∈ Icc 0 ψ, c.R x (f x) ≤ H x) :
    -(c.Vp ψ * c.D ψ (f ψ) * f' ψ) ≤ ∫ x in (0 : ℝ)..ψ, c.Vp x * H x := by
  rw [steady_flux_eq_integral c hψ hV hD hf hpos hsteady hcont hint haxis]
  exact integral_mono_on hψ hint hintH
    (fun x hx => mul_le_mul_of_nonneg_left (hRH x hx) (hVnn x hx))

end PlasmaLean.Transport.Stiff
