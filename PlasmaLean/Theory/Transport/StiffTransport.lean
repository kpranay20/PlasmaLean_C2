/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Stiff (critical-gradient) turbulent transport: a model class and the core-temperature cap

Note N-45 (`notes/theory/stiff-turbulent-transport.md`), question Q-33, layer 1 of the
turbulence programme for contract clauses C2/C5.

## Why

Microturbulence (ITG, TEM, ETG) is present in every hot magnetized plasma with gradients,
whatever the geometry. What geometry changes is the **critical gradient** above which the
turbulent heat flux switches on, and the **stiffness** of the flux above it. The radial transport
kernel (`Kernel/Transport`) only asks `D(ψ,T) ≥ 0`, so it cannot express this, and a C5 claim
can silently assume too little turbulence. This file states turbulence as a **lower bound on the
heat flux** (a floor) that every admissible turbulence law must satisfy, and proves the
consequences for *every* law in the class. Since more transport only lowers the core
temperature, an upper bound on the core temperature needs only the floor.

## Model (steady state, flux-surface averaged)

* `ψ ∈ [0,1]`: a normalized flux label, magnetic axis at `ψ = 0`, edge at `ψ = 1`.
* `T ψ > 0`: the temperature profile, with derivative `T' ψ` in the interior.
* `logGrad T T' = −T'/T`: the inverse temperature-gradient length in the `ψ` coordinate.
* `Q ψ`: the outward heat flow (W) through the surface `ψ`.
* **Turbulent floor** (`StiffFloorAt`): `S ψ · T ψ · (logGrad − κ ψ)₊ ≤ Q ψ`, with a stiffness
  weight `S ψ > 0` and a critical log-gradient `κ ψ` (both in `ψ` units, both supplied by the
  turbulence model; the geometry enters through them).
* **Power balance**: `Q ψ ≤ W ψ`, the heating power deposited inside `ψ` (at a steady state
  `Q = W − radiation`), and `W ψ ≤ w̄ · S ψ` (a bound on heating power per stiffness).

The floor is a hypothesis on the realized profile, so it applies to solutions of the kernel
equation as well: with `Q = V' D(ψ,T) (−T')` the floor is a lower bound on `D` along the
solution. It is not a kernel law.

**Coordinates.** For `ψ = ρ²` (`ρ = r/a`), `logGrad = (a/L_T)/(2ρ)`, so a constant physical
critical gradient `(a/L_T)_crit` gives `κ ψ = (a/L_T)_crit/(2ρ)`, unbounded at the axis. Only
its integral enters the general bound: `∫₀¹ κ dψ = ∫₀¹ (a/L_T)_crit dρ`. Hence `core_le` takes
an antiderivative `K` of a majorant `κ̂ ≥ κ`, and `core_le_const` (sharp, constant `κ̄`) is for
coordinates in which `κ` is bounded.

## Results

* `neg_deriv_le`: pointwise, `−T' ≤ κ T + w̄` (gradient clamping by stiffness).
* `core_le`: `T 0 ≤ (T 1 + w̄) · exp (K 1 − K 0)`, with `K' = κ̂ ≥ κ`, `κ̂ ≥ 0`.
* `core_le_const`: `T 0 ≤ T 1 · e^{κ̄} + (w̄/κ̄)(e^{κ̄} − 1)` for `κ ≤ κ̄`, `κ̄ > 0`; sharp
  (`sharpProfile_stiffSteady`, `sharpProfile_zero`).
* `core_lt_of_cap_lt`, `core_lt_of_cap_lt_const`: **no access** to a core temperature above the
  cap, for every turbulence law in the class.
* `stiff_limit`: with `w̄ = 0` (infinitely stiff), `T 0 ≤ T 1 · e^{κ̄}`.

## Sanity

* the standard critical-gradient model flux `Q = S₀ T g (g − κ)₊` (`g = logGrad`, `κ ≥ 0`)
  satisfies the floor with `S = S₀ κ` (`stiffFloorAt_criticalGradient`);
* zero transport is excluded above threshold: with `Q = 0` the floor forces `logGrad ≤ κ`
  (`logGrad_le_of_floor_zero`);
* the bound is attained by an explicit profile (`sharpProfile`).

**Not covered.** The values of `κ` and `S` (they come from the turbulence physics; layer 2,
N-45 §4); time-dependent profiles; the derivation of the integrated power balance from the
kernel PDE; electrons and ions separately (one temperature).
-/

public section
noncomputable section

namespace PlasmaLean.Transport.Stiff

open Set Real

/-! ## Definitions -/

/-- The inverse temperature-gradient length in the flux coordinate, `g = −T'/T`. -/
@[expose] def logGrad (T T' : ℝ) : ℝ := -T' / T

/-- **Turbulent floor at one surface**: the heat flow `Q` is at least the stiff critical-gradient
flux `S · T · (g − κ)₊`, with `g = logGrad T T'`. -/
@[expose] def StiffFloorAt (S κ T T' Q : ℝ) : Prop :=
  S * T * max 0 (logGrad T T' - κ) ≤ Q

/-- **A steady profile under stiff turbulent transport** on `ψ ∈ [0,1]` (axis `0`, edge `1`):
the temperature `T` is continuous on `[0,1]`, positive with derivative `T'` in the interior; the
heat flow `Q` obeys the turbulent floor with stiffness `S > 0` and critical log-gradient `κ`;
`Q ≤ W` (heating power inside `ψ`); and `W ≤ w̄ S`. -/
structure StiffSteadyProfile (T T' Q W S κ : ℝ → ℝ) (wbar : ℝ) : Prop where
  /-- `T` is continuous up to the axis and the edge. -/
  cont : ContinuousOn T (Icc 0 1)
  /-- `T'` is the derivative of `T` in the interior. -/
  deriv : ∀ ψ ∈ Ioo (0 : ℝ) 1, HasDerivAt T (T' ψ) ψ
  /-- The temperature is positive. -/
  T_pos : ∀ ψ ∈ Ioo (0 : ℝ) 1, 0 < T ψ
  /-- The stiffness weight is positive. -/
  S_pos : ∀ ψ ∈ Ioo (0 : ℝ) 1, 0 < S ψ
  /-- The turbulent floor. -/
  floor : ∀ ψ ∈ Ioo (0 : ℝ) 1, StiffFloorAt (S ψ) (κ ψ) (T ψ) (T' ψ) (Q ψ)
  /-- Steady power balance: the heat flow is at most the heating power inside `ψ`. -/
  balance : ∀ ψ ∈ Ioo (0 : ℝ) 1, Q ψ ≤ W ψ
  /-- Heating power per stiffness is bounded by `w̄`. -/
  power : ∀ ψ ∈ Ioo (0 : ℝ) 1, W ψ ≤ wbar * S ψ

/-! ## Pointwise clamping -/

/-- **Gradient clamping.** Under the floor and the power bounds, `−T' ≤ κ̄ T + w̄` for any
`κ̄ ≥ κ`. -/
theorem neg_deriv_le {S κ T T' Q W κbar wbar : ℝ} (hS : 0 < S) (hT : 0 < T)
    (hfl : StiffFloorAt S κ T T' Q) (hQ : Q ≤ W) (hW : W ≤ wbar * S) (hκ : κ ≤ κbar) :
    -T' ≤ κbar * T + wbar := by
  unfold StiffFloorAt logGrad at hfl
  set m := max 0 (-T' / T - κ)
  have h1 : S * (T * m) ≤ S * wbar := by
    calc S * (T * m) = S * T * m := by ring
      _ ≤ wbar * S := hfl.trans (hQ.trans hW)
      _ = S * wbar := by ring
  have h2 : T * m ≤ wbar := le_of_mul_le_mul_left h1 hS
  have h3 : T * (-T' / T - κ) ≤ wbar :=
    (mul_le_mul_of_nonneg_left (le_max_right _ _) hT.le).trans h2
  have h4 : T * (-T' / T) = -T' := by
    rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self hT.ne', mul_one]
  rw [mul_sub, h4] at h3
  have h5 : T * κ ≤ T * κbar := mul_le_mul_of_nonneg_left hκ hT.le
  linarith

/-! ## The core-temperature cap -/

/-- **Core-temperature cap (general form).** For every steady profile in the stiff class, with
`κ ≤ κ̂`, `κ̂ ≥ 0` and `K` an antiderivative of `κ̂` (continuous on `[0,1]`),
`T 0 ≤ (T 1 + w̄) · exp (K 1 − K 0)`. For `ψ = ρ²` and a constant physical threshold,
`K 1 − K 0 = (a/L_T)_crit`. -/
theorem core_le {T T' Q W S κ κhat K : ℝ → ℝ} {wbar : ℝ}
    (h : StiffSteadyProfile T T' Q W S κ wbar) (hw : 0 ≤ wbar)
    (hK : ContinuousOn K (Icc 0 1)) (hKd : ∀ ψ ∈ Ioo (0 : ℝ) 1, HasDerivAt K (κhat ψ) ψ)
    (hκ : ∀ ψ ∈ Ioo (0 : ℝ) 1, κ ψ ≤ κhat ψ) (hκ0 : ∀ ψ ∈ Ioo (0 : ℝ) 1, 0 ≤ κhat ψ) :
    T 0 ≤ (T 1 + wbar) * exp (K 1 - K 0) := by
  have h01 : (0 : ℝ) ≤ 1 := zero_le_one
  -- `K` is nondecreasing.
  have hKmono : MonotoneOn K (Icc 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1) hK
    · rw [interior_Icc]
      exact fun ψ hψ => (hKd ψ hψ).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro ψ hψ
      rw [(hKd ψ hψ).deriv]
      exact hκ0 ψ hψ
  -- `G ψ = T ψ e^{K ψ} + w̄ e^{K 1} ψ` is nondecreasing.
  have hGd : ∀ ψ ∈ Ioo (0 : ℝ) 1, HasDerivAt
      (fun x => T x * exp (K x) + wbar * exp (K 1) * x)
      (T' ψ * exp (K ψ) + T ψ * (exp (K ψ) * κhat ψ) + wbar * exp (K 1) * 1) ψ :=
    fun ψ hψ => ((h.deriv ψ hψ).mul (hKd ψ hψ).exp).add
      ((hasDerivAt_id' ψ).const_mul (wbar * exp (K 1)))
  have hGmono : MonotoneOn (fun x => T x * exp (K x) + wbar * exp (K 1) * x) (Icc 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
    · exact (h.cont.mul (continuous_exp.comp_continuousOn hK)).add
        ((continuous_const.mul continuous_id).continuousOn)
    · rw [interior_Icc]
      exact fun ψ hψ => (hGd ψ hψ).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro ψ hψ
      rw [(hGd ψ hψ).deriv]
      have e1 := neg_deriv_le (h.S_pos ψ hψ) (h.T_pos ψ hψ) (h.floor ψ hψ) (h.balance ψ hψ)
        (h.power ψ hψ) (hκ ψ hψ)
      have hE : exp (K ψ) ≤ exp (K 1) :=
        exp_le_exp.2 (hKmono (Ioo_subset_Icc_self hψ) (right_mem_Icc.2 h01) hψ.2.le)
      have hpos := exp_pos (K ψ)
      have a1 := mul_le_mul_of_nonneg_right e1 hpos.le
      have a2 := mul_le_mul_of_nonneg_left hE hw
      nlinarith
  have hG := hGmono (left_mem_Icc.2 h01) (right_mem_Icc.2 h01) h01
  simp only [mul_zero, add_zero, mul_one] at hG
  rw [exp_sub, ← mul_div_assoc, le_div_iff₀ (exp_pos _)]
  have e : (T 1 + wbar) * exp (K 1) = T 1 * exp (K 1) + wbar * exp (K 1) := by ring
  linarith

/-- **Core-temperature cap (constant threshold, sharp).** If `κ ≤ κ̄` with `κ̄ > 0`, then
`T 0 ≤ T 1 · e^{κ̄} + (w̄/κ̄)(e^{κ̄} − 1)`. Equality holds for `sharpProfile`. -/
theorem core_le_const {T T' Q W S κ : ℝ → ℝ} {wbar κbar : ℝ}
    (h : StiffSteadyProfile T T' Q W S κ wbar) (hκbar : 0 < κbar)
    (hκ : ∀ ψ ∈ Ioo (0 : ℝ) 1, κ ψ ≤ κbar) :
    T 0 ≤ T 1 * exp κbar + wbar / κbar * (exp κbar - 1) := by
  have h01 : (0 : ℝ) ≤ 1 := zero_le_one
  have hk0 : κbar ≠ 0 := hκbar.ne'
  set c := wbar / κbar with hc
  have hcc : κbar * c = wbar := by
    rw [hc, mul_div_assoc', mul_comm, mul_div_assoc, div_self hk0, mul_one]
  have hFd : ∀ ψ ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun x => (T x + c) * exp (κbar * x))
      (T' ψ * exp (κbar * ψ) + (T ψ + c) * (exp (κbar * ψ) * (κbar * 1))) ψ :=
    fun ψ hψ => ((h.deriv ψ hψ).add_const c).mul ((hasDerivAt_id' ψ).const_mul κbar).exp
  have hFmono : MonotoneOn (fun x => (T x + c) * exp (κbar * x)) (Icc 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
    · exact (h.cont.add continuousOn_const).mul
        ((continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn)
    · rw [interior_Icc]
      exact fun ψ hψ => (hFd ψ hψ).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro ψ hψ
      rw [(hFd ψ hψ).deriv]
      have e1 := neg_deriv_le (h.S_pos ψ hψ) (h.T_pos ψ hψ) (h.floor ψ hψ) (h.balance ψ hψ)
        (h.power ψ hψ) (hκ ψ hψ)
      have hpos := exp_pos (κbar * ψ)
      have key : 0 ≤ T' ψ + κbar * (T ψ + c) := by
        have : κbar * (T ψ + c) = κbar * T ψ + wbar := by rw [mul_add, hcc]
        linarith
      have := mul_nonneg key hpos.le
      nlinarith
  have hF := hFmono (left_mem_Icc.2 h01) (right_mem_Icc.2 h01) h01
  simp only [mul_zero, exp_zero, mul_one] at hF
  calc T 0 ≤ (T 1 + c) * exp κbar - c := by linarith
    _ = T 1 * exp κbar + c * (exp κbar - 1) := by ring

/-- **Stiff limit.** With `w̄ = 0` (heating power negligible against stiffness),
`T 0 ≤ T 1 · e^{κ̄}`: the core can exceed the edge only by the critical-gradient factor. -/
theorem stiff_limit {T T' Q W S κ : ℝ → ℝ} {κbar : ℝ}
    (h : StiffSteadyProfile T T' Q W S κ 0) (hκbar : 0 < κbar)
    (hκ : ∀ ψ ∈ Ioo (0 : ℝ) 1, κ ψ ≤ κbar) :
    T 0 ≤ T 1 * exp κbar := by
  have := core_le_const h hκbar hκ
  simpa using this

/-- **No access above the cap (general form).** If the cap is below a target core temperature
`T_burn`, then no steady profile in the stiff class reaches it, whatever turbulence law
realizes the floor. -/
theorem core_lt_of_cap_lt {T T' Q W S κ κhat K : ℝ → ℝ} {wbar Tburn : ℝ}
    (h : StiffSteadyProfile T T' Q W S κ wbar) (hw : 0 ≤ wbar)
    (hK : ContinuousOn K (Icc 0 1)) (hKd : ∀ ψ ∈ Ioo (0 : ℝ) 1, HasDerivAt K (κhat ψ) ψ)
    (hκ : ∀ ψ ∈ Ioo (0 : ℝ) 1, κ ψ ≤ κhat ψ) (hκ0 : ∀ ψ ∈ Ioo (0 : ℝ) 1, 0 ≤ κhat ψ)
    (hcap : (T 1 + wbar) * exp (K 1 - K 0) < Tburn) :
    T 0 < Tburn :=
  (core_le h hw hK hKd hκ hκ0).trans_lt hcap

/-- **No access above the cap (constant threshold).** -/
theorem core_lt_of_cap_lt_const {T T' Q W S κ : ℝ → ℝ} {wbar κbar Tburn : ℝ}
    (h : StiffSteadyProfile T T' Q W S κ wbar) (hκbar : 0 < κbar)
    (hκ : ∀ ψ ∈ Ioo (0 : ℝ) 1, κ ψ ≤ κbar)
    (hcap : T 1 * exp κbar + wbar / κbar * (exp κbar - 1) < Tburn) :
    T 0 < Tburn :=
  (core_le_const h hκbar hκ).trans_lt hcap

/-! ## Sanity: the class contains the critical-gradient model, excludes zero transport, and the
cap is sharp -/

/-- **Witness: the critical-gradient model is in the class.** The flux
`Q = S₀ T g (g − κ)₊` (`χ = χ_s (g − κ)₊`, flux `∝ χ T g`) satisfies the floor with stiffness
`S₀ κ`, for `S₀ ≥ 0`, `T > 0` (the class needs `S₀ κ > 0`, i.e. `S₀, κ > 0`). -/
theorem stiffFloorAt_criticalGradient {S0 κ T T' : ℝ} (hS0 : 0 ≤ S0) (hT : 0 < T) :
    StiffFloorAt (S0 * κ) κ T T'
      (S0 * T * logGrad T T' * max 0 (logGrad T T' - κ)) := by
  unfold StiffFloorAt
  set g := logGrad T T'
  have hm : 0 ≤ max 0 (g - κ) := le_max_left _ _
  have key : κ * max 0 (g - κ) ≤ g * max 0 (g - κ) := by
    rcases le_total g κ with hg | hg
    · rw [max_eq_left (by linarith)]
      simp
    · exact mul_le_mul_of_nonneg_right hg hm
  have := mul_le_mul_of_nonneg_left key (mul_nonneg hS0 hT.le)
  nlinarith

/-- **Zero transport is excluded above threshold.** If the heat flow vanishes, the floor forces
the gradient to stay at or below the critical one. -/
theorem logGrad_le_of_floor_zero {S κ T T' : ℝ} (hS : 0 < S) (hT : 0 < T)
    (h : StiffFloorAt S κ T T' 0) : logGrad T T' ≤ κ := by
  unfold StiffFloorAt at h
  have hm : max 0 (logGrad T T' - κ) ≤ 0 := by
    by_contra hc
    have := mul_pos (mul_pos hS hT) (lt_of_not_ge hc)
    linarith
  linarith [le_max_right 0 (logGrad T T' - κ)]

/-- The profile attaining `core_le_const`:
`T(ψ) = (T₁ + w̄/κ̄) e^{κ̄(1−ψ)} − w̄/κ̄`, the solution of `−T' = κ̄ T + w̄`, `T(1) = T₁`. -/
@[expose] def sharpProfile (T1 κbar wbar ψ : ℝ) : ℝ :=
  (T1 + wbar / κbar) * exp (κbar * (1 - ψ)) - wbar / κbar

/-- `sharpProfile` solves `T' = −(κ̄ T + w̄)`. -/
theorem sharpProfile_hasDerivAt (T1 κbar wbar ψ : ℝ) (hκ : κbar ≠ 0) :
    HasDerivAt (sharpProfile T1 κbar wbar) (-(κbar * sharpProfile T1 κbar wbar ψ + wbar)) ψ := by
  have h1 : HasDerivAt (fun x : ℝ => κbar * (1 - x)) (κbar * (-1)) ψ :=
    ((hasDerivAt_id' ψ).const_sub 1).const_mul κbar
  have h2 := (h1.exp.const_mul (T1 + wbar / κbar)).sub_const (wbar / κbar)
  have hcc : κbar * (wbar / κbar) = wbar := by
    rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self hκ, mul_one]
  refine h2.congr_deriv ?_
  simp only [sharpProfile]
  linear_combination -hcc

/-- Edge value: `sharpProfile T₁ κ̄ w̄ 1 = T₁`. -/
theorem sharpProfile_one (T1 κbar wbar : ℝ) : sharpProfile T1 κbar wbar 1 = T1 := by
  simp [sharpProfile]

/-- Core value: `sharpProfile T₁ κ̄ w̄ 0 = T₁ e^{κ̄} + (w̄/κ̄)(e^{κ̄} − 1)`, the cap of
`core_le_const`. -/
theorem sharpProfile_zero (T1 κbar wbar : ℝ) :
    sharpProfile T1 κbar wbar 0 = T1 * exp κbar + wbar / κbar * (exp κbar - 1) := by
  simp only [sharpProfile, sub_zero, mul_one]
  ring

/-- `sharpProfile` is at least `T₁ > 0` on `ψ ≤ 1` (for `κ̄ > 0`, `w̄ ≥ 0`). -/
theorem sharpProfile_ge (T1 κbar wbar ψ : ℝ) (hκ : 0 < κbar) (hw : 0 ≤ wbar) (hT1 : 0 ≤ T1)
    (hψ : ψ ≤ 1) : T1 ≤ sharpProfile T1 κbar wbar ψ := by
  have hc0 : 0 ≤ wbar / κbar := div_nonneg hw hκ.le
  have he : 1 ≤ exp (κbar * (1 - ψ)) := one_le_exp (mul_nonneg hκ.le (by linarith))
  have := mul_le_mul_of_nonneg_left he (by linarith : 0 ≤ T1 + wbar / κbar)
  simp only [sharpProfile]
  linarith

/-- If `−T' = κ T + w` with `T > 0`, `w ≥ 0`, the stiff flux `T (g − κ)₊` equals `w`. -/
theorem stiffFlux_eq_of_ode {T T' κ w : ℝ} (hT : 0 < T) (hw : 0 ≤ w)
    (h : -T' = κ * T + w) : T * max 0 (logGrad T T' - κ) = w := by
  have e : logGrad T T' - κ = w / T := by
    unfold logGrad
    rw [h, add_div, mul_div_assoc, div_self hT.ne', mul_one]
    ring
  rw [e, max_eq_right (div_nonneg hw hT.le), mul_div_assoc', mul_comm, mul_div_assoc,
    div_self hT.ne', mul_one]

/-- **Sharpness.** `sharpProfile` is a steady profile in the stiff class with `S = 1`,
`κ = κ̄`, `Q = W = w̄`, so `core_le_const` cannot be improved. -/
theorem sharpProfile_stiffSteady (T1 κbar wbar : ℝ) (hκ : 0 < κbar) (hw : 0 ≤ wbar)
    (hT1 : 0 < T1) :
    StiffSteadyProfile (sharpProfile T1 κbar wbar)
      (fun ψ => -(κbar * sharpProfile T1 κbar wbar ψ + wbar))
      (fun _ => wbar) (fun _ => wbar) (fun _ => 1) (fun _ => κbar) wbar where
  cont := by
    have : Continuous (sharpProfile T1 κbar wbar) := by
      unfold sharpProfile
      fun_prop
    exact this.continuousOn
  deriv := fun ψ _ => sharpProfile_hasDerivAt T1 κbar wbar ψ hκ.ne'
  T_pos := fun ψ hψ => hT1.trans_le (sharpProfile_ge T1 κbar wbar ψ hκ hw hT1.le hψ.2.le)
  S_pos := fun _ _ => one_pos
  floor := by
    intro ψ hψ
    have hTp : 0 < sharpProfile T1 κbar wbar ψ :=
      hT1.trans_le (sharpProfile_ge T1 κbar wbar ψ hκ hw hT1.le hψ.2.le)
    change StiffFloorAt 1 κbar (sharpProfile T1 κbar wbar ψ)
      (-(κbar * sharpProfile T1 κbar wbar ψ + wbar)) wbar
    unfold StiffFloorAt
    rw [one_mul, stiffFlux_eq_of_ode (κ := κbar) hTp hw (neg_neg _)]
  balance := fun _ _ => le_rfl
  power := fun _ _ => by simp

end PlasmaLean.Transport.Stiff
