/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.ITGAvailableEnergy

/-!
# Stability windows of the ITG available energy in isodynamic flux tubes

Note N-47 §6, question Q-35 (b). Source: Mackenbach et al., J. Plasma Phys. 91 (2025) E144,
§2.3.2, eqs. 2.28–2.39.

## Setting (one point `ℓ` of an isodynamic tube, `ω_ψ = κ_ψ = 0`)

Normalized velocity variables `x = μB₀/T₀ ≥ 0`, `y = m v∥²/(2T₀) ≥ 0`, density-gradient frequency
`N = T₀ d ln n/dψ ≠ 0`, `η = d ln T/d ln n`, `η_B = (∂_ψ ln B)/(d ln n/dψ)`, ground-state parameter
`κ = κ_α(ℓ)` (independent of `x`, `y`). With `ε ≈ μB₀ + m v∥²/2` (the source's eq. 2.29):

* `ω*^T − ω_α = N · brk`, `brk = 1 − 3η/2 + η y + x (η − η_B)` (`brk`, `Pf`);
* `κ_α + ω_α = κ + x N η_B` (`Qf`).

The integrand is `2 Δψ² (Q P)₊` (`itg_isodynamic_eq`), so it vanishes at a point iff `Q P ≤ 0`.
`η_B < 0` is **good curvature** for a peaked density (`d ln n/dψ < 0`, `∂_ψ B|_α > 0`).

## Results

* `good_curvature_stable_iff`: for `η_B < 0`, some `κ` makes the integrand vanish at every
  `(x, y)` **iff** `0 ≤ η ≤ 2/3` (agrees with the source); for such `η` the choice `κ = −N`
  also satisfies the ground-state constraint pointwise (`good_curvature_ground_state`).
* `bad_curvature_not_attained`: for `η_B > 0` and `η ≠ 0`, **every finite** `κ` leaves a point
  with a positive integrand. In the source's bad-curvature window `0 < η_B ≤ η ≤ 2/3` this only
  says the zero is **not attained**: there `κ_α + ω_α = κ + x N η_B` cannot have the sign
  `−σ(ω*^T − ω_α)` for all `x ≥ 0` (`Qf_eventually_sign`), so the isodynamic density constraint
  (2.36) has no exact solution, but the offending points lie at `x ≳ κ/(N η_B)`, where the
  Maxwellian weight is `≈ e^{−x}`. An independent numerical solution of the source's
  eqs. 2.15/2.17a/2.21 (N-47 §6) shows the constraint residual and `A` decaying like that weight as
  `κ → ∞`: the source's claim `A = 0` holds as an **infimum**. Outside the window (`η < 0`,
  `0 < η < η_B`, `η > 2/3`) the positive points sit at bounded `x` and the instability is genuine.
* `eta_zero_stable`: with `η = 0`, `κ = −N` makes the integrand vanish for **every** `η_B`, so
  the source's "η ≥ η_B is necessary" fails at the boundary `η = 0` (its eq. 2.32 argument needs
  `η ≠ 0`).
* The building blocks `unstable_of_eta_gt` (`η > 2/3`), `unstable_of_eta_neg` (`η < 0`),
  `unstable_of_lt_etaB` (`0 < η < η_B`), and `bad_curvature_window_not_attained`
  (`0 < η_B ≤ η ≤ 2/3`, where only attainment fails).

**Not covered.** The integrated statements (these are pointwise in `(x, y)`, which is what the
vanishing of a continuous integrand with a positive Maxwellian weight reduces to); the
non-isodynamic case; a Lean proof that `A(κ) → 0` as `κ → ∞` in the bad-curvature window (only
observed numerically).
-/

public section
noncomputable section

namespace PlasmaLean.Kinetic.ITGAE

/-- The bracket of eq. 2.29: `1 − 3η/2 + η y + x (η − η_B)`. -/
@[expose] def brk (η ηB x y : ℝ) : ℝ := 1 - 3 / 2 * η + η * y + x * (η - ηB)

/-- `ω*^T − ω_α = N · brk`. -/
@[expose] def Pf (N η ηB x y : ℝ) : ℝ := N * brk η ηB x y

/-- `κ_α + ω_α = κ + x N η_B`. -/
@[expose] def Qf (κ N ηB x : ℝ) : ℝ := κ + x * N * ηB

/-- The isodynamic ITG integrand is `2 Δψ² (Q P)₊`. -/
theorem itg_isodynamic_eq (Δψ Δα ωα ωs κα : ℝ) :
    itgIntegrand Δψ Δα ωα 0 ωs κα 0 = 2 * max 0 (Δψ ^ 2 * ((κα + ωα) * (ωs - ωα))) := by
  simp only [itgIntegrand, sub_zero, mul_zero]
  rw [aeIntegrand_isodynamic]
  congr 2
  ring

/-- The integrand at `(x, y)` in the window variables: with `ω_α = x N η_B` and
`ω*^T = ω_α + N brk`, it is `2 Δψ² (Q P)₊`. -/
theorem itg_window_eq (Δψ Δα κ N η ηB x y : ℝ) :
    itgIntegrand Δψ Δα (x * N * ηB) 0 (x * N * ηB + Pf N η ηB x y) κ 0 =
      2 * max 0 (Δψ ^ 2 * (Qf κ N ηB x * Pf N η ηB x y)) := by
  rw [itg_isodynamic_eq]
  simp only [Qf, add_sub_cancel_left]

/-! ## Sign changes -/

/-- If `brk(x₀, ·)` takes both signs on `y ≥ 0` and `Q(x₀) ≠ 0`, some point has `Q P > 0`. -/
theorem exists_pos_of_sign_change {κ N η ηB x₀ y₁ y₂ : ℝ} (hN : N ≠ 0)
    (hQ : Qf κ N ηB x₀ ≠ 0) (h1 : brk η ηB x₀ y₁ < 0) (h2 : 0 < brk η ηB x₀ y₂) :
    0 < Qf κ N ηB x₀ * Pf N η ηB x₀ y₁ ∨ 0 < Qf κ N ηB x₀ * Pf N η ηB x₀ y₂ := by
  simp only [Pf]
  rcases lt_or_gt_of_ne (mul_ne_zero hQ hN) with h | h
  · left; nlinarith
  · right; nlinarith

/-- Along `y`, `brk(x₀, ·)` has slope `η`: if `η brk(x₀, 0) < 0`, it takes both signs on
`y ≥ 0`. -/
theorem brk_both_signs {η ηB x₀ : ℝ} (h : η * brk η ηB x₀ 0 < 0) :
    ∃ y₁ y₂, 0 ≤ y₁ ∧ 0 ≤ y₂ ∧ brk η ηB x₀ y₁ < 0 ∧ 0 < brk η ηB x₀ y₂ := by
  set b := brk η ηB x₀ 0 with hb
  have hy : ∀ y, brk η ηB x₀ y = b + η * y := by intro y; simp only [hb, brk]; ring
  rcases lt_or_gt_of_ne (show η ≠ 0 by rintro rfl; simp at h) with hη | hη
  · have hb0 : 0 < b := by nlinarith
    have hη0 : η ≠ 0 := hη.ne
    refine ⟨(b + 1) / (-η), 0, div_nonneg (by linarith) (by linarith), le_rfl, ?_, ?_⟩
    · rw [hy, show η * ((b + 1) / -η) = -(b + 1) by field_simp]; linarith
    · rw [hy]; simpa using hb0
  · have hb0 : b < 0 := by nlinarith
    have hη0 : η ≠ 0 := hη.ne'
    refine ⟨0, (-b + 1) / η, le_rfl, div_nonneg (by linarith) hη.le, ?_, ?_⟩
    · rw [hy]; simpa using hb0
    · rw [hy, show η * ((-b + 1) / η) = -b + 1 by field_simp]; linarith

/-- An affine `Q` that is not identically zero is nonzero at one of two distinct points. -/
theorem Qf_ne_zero_of_two {κ N ηB x₁ x₂ : ℝ} (hx : x₁ ≠ x₂) (hs : N * ηB ≠ 0) :
    Qf κ N ηB x₁ ≠ 0 ∨ Qf κ N ηB x₂ ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨h1, h2⟩ := h
  simp only [Qf] at h1 h2
  have : (x₁ - x₂) * (N * ηB) = 0 := by linarith
  rcases mul_eq_zero.1 this with h | h
  · exact hx (sub_eq_zero.1 h)
  · exact hs h

/-- **Instability from two points.** If at two distinct `x₁, x₂ ≥ 0` the bracket at `y = 0` has
the sign opposite to `η`, then every `κ` leaves a point with `Q P > 0`. -/
theorem unstable_of_two_points {κ N η ηB x₁ x₂ : ℝ} (hN : N ≠ 0) (hB : ηB ≠ 0) (hx : x₁ ≠ x₂)
    (hx₁ : 0 ≤ x₁) (hx₂ : 0 ≤ x₂) (h₁ : η * brk η ηB x₁ 0 < 0) (h₂ : η * brk η ηB x₂ 0 < 0) :
    ∃ x y, 0 ≤ x ∧ 0 ≤ y ∧ 0 < Qf κ N ηB x * Pf N η ηB x y := by
  have go : ∀ x₀, 0 ≤ x₀ → η * brk η ηB x₀ 0 < 0 → Qf κ N ηB x₀ ≠ 0 →
      ∃ x y, 0 ≤ x ∧ 0 ≤ y ∧ 0 < Qf κ N ηB x * Pf N η ηB x y := by
    intro x₀ hx₀ hs hQ
    obtain ⟨y₁, y₂, hy₁, hy₂, hb₁, hb₂⟩ := brk_both_signs hs
    rcases exists_pos_of_sign_change hN hQ hb₁ hb₂ with h | h
    · exact ⟨x₀, y₁, hx₀, hy₁, h⟩
    · exact ⟨x₀, y₂, hx₀, hy₂, h⟩
  rcases Qf_ne_zero_of_two (κ := κ) hx (mul_ne_zero hN hB) with h | h
  · exact go x₁ hx₁ h₁ h
  · exact go x₂ hx₂ h₂ h

/-! ## The windows -/

/-- **`η > 2/3` is unstable** (any curvature, `η_B ≠ 0`). -/
theorem unstable_of_eta_gt {κ N η ηB : ℝ} (hN : N ≠ 0) (hB : ηB ≠ 0) (hη : 2 / 3 < η) :
    ∃ x y, 0 ≤ x ∧ 0 ≤ y ∧ 0 < Qf κ N ηB x * Pf N η ηB x y := by
  set u := 3 / 2 * η - 1 with hu
  set d := |η - ηB| with hd
  have hu0 : 0 < u := by rw [hu]; linarith
  have hd0 : 0 ≤ d := abs_nonneg _
  set δ := u / (2 * (d + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδd : δ * (d + 1) = u / 2 := by rw [hδ]; field_simp
  have hle : δ * (η - ηB) ≤ δ * d := mul_le_mul_of_nonneg_left (le_abs_self _) hδ0.le
  refine unstable_of_two_points hN hB (ne_of_lt hδ0) le_rfl hδ0.le ?_ ?_
  · have : brk η ηB 0 0 = -u := by simp only [brk, hu]; ring
    rw [this]; nlinarith
  · have : brk η ηB δ 0 < 0 := by
      have e : brk η ηB δ 0 = -u + δ * (η - ηB) := by simp only [brk, hu]; ring
      rw [e]; nlinarith
    nlinarith

/-- **`η < 0` is unstable** (any curvature, `η_B ≠ 0`). -/
theorem unstable_of_eta_neg {κ N η ηB : ℝ} (hN : N ≠ 0) (hB : ηB ≠ 0) (hη : η < 0) :
    ∃ x y, 0 ≤ x ∧ 0 ≤ y ∧ 0 < Qf κ N ηB x * Pf N η ηB x y := by
  set c := 1 - 3 / 2 * η with hc
  set d := |η - ηB| with hd
  have hc0 : 0 < c := by rw [hc]; linarith
  have hd0 : 0 ≤ d := abs_nonneg _
  set δ := c / (2 * (d + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδd : δ * (d + 1) = c / 2 := by rw [hδ]; field_simp
  have hle : -(δ * d) ≤ δ * (η - ηB) := by
    have := neg_abs_le (η - ηB)
    nlinarith
  refine unstable_of_two_points hN hB (ne_of_lt hδ0) le_rfl hδ0.le ?_ ?_
  · have : brk η ηB 0 0 = c := by simp only [brk, hc]; ring
    rw [this]; nlinarith
  · have : 0 < brk η ηB δ 0 := by
      have e : brk η ηB δ 0 = c + δ * (η - ηB) := by simp only [brk, hc]; ring
      rw [e]; nlinarith
    nlinarith

/-- **`0 < η < η_B` is unstable** (the source's necessity of `η ≥ η_B`, valid for `η > 0`). -/
theorem unstable_of_lt_etaB {κ N η ηB : ℝ} (hN : N ≠ 0) (hη : 0 < η) (hlt : η < ηB) :
    ∃ x y, 0 ≤ x ∧ 0 ≤ y ∧ 0 < Qf κ N ηB x * Pf N η ηB x y := by
  set c := 1 - 3 / 2 * η with hc
  set g := ηB - η with hg
  have hg0 : 0 < g := by rw [hg]; linarith
  set X := |c| / g + 1 with hX
  have hX0 : 0 < X := by positivity
  have hXg : |c| < X * g := by
    rw [hX, add_mul, div_mul_cancel₀ _ hg0.ne']; linarith
  have hb : ∀ x, X ≤ x → brk η ηB x 0 < 0 := by
    intro x hx
    have e : brk η ηB x 0 = c - x * g := by simp only [brk, hc, hg]; ring
    rw [e]
    have : X * g ≤ x * g := mul_le_mul_of_nonneg_right hx hg0.le
    linarith [le_abs_self c]
  refine unstable_of_two_points hN (by linarith) (show X ≠ X + 1 by linarith) hX0.le
    (by linarith) ?_ ?_
  · nlinarith [hb X le_rfl]
  · nlinarith [hb (X + 1) (by linarith)]

/-- For `η_B > 0`, `Q` eventually has the sign of `N`: `Q(x) N > 0` for large `x`. So no `κ`
gives `σ(Q) = −σ(N)` on all of `x ≥ 0`, as a ground state with `σ(P) = σ(N)` would need. -/
theorem Qf_eventually_sign {κ N ηB : ℝ} (hN : N ≠ 0) (hB : 0 < ηB) :
    ∃ X, 0 ≤ X ∧ ∀ x, X ≤ x → 0 < Qf κ N ηB x * N := by
  have hN2 : 0 < N ^ 2 := by positivity
  refine ⟨|κ * N| / (N ^ 2 * ηB) + 1, by positivity, fun x hx => ?_⟩
  have e : Qf κ N ηB x * N = κ * N + x * (N ^ 2 * ηB) := by simp only [Qf]; ring
  rw [e]
  have hp : 0 < N ^ 2 * ηB := by positivity
  have : |κ * N| < x * (N ^ 2 * ηB) := by
    have h1 : (|κ * N| / (N ^ 2 * ηB) + 1) * (N ^ 2 * ηB) ≤ x * (N ^ 2 * ηB) :=
      mul_le_mul_of_nonneg_right hx hp.le
    rw [add_mul, div_mul_cancel₀ _ hp.ne'] at h1
    linarith
  linarith [neg_abs_le (κ * N)]

/-- **The source's bad-curvature window: the zero is not attained.** For `0 < η_B ≤ η ≤ 2/3`, every
finite `κ` leaves a point with `Q P > 0`; the point lies at `x ≳ κ/(N η_B)`, so the available
energy can still tend to `0` as `κ → ∞` (observed numerically, N-47 §6). -/
theorem bad_curvature_window_not_attained {κ N η ηB : ℝ} (hN : N ≠ 0) (hB : 0 < ηB) (hle : ηB ≤ η)
    (hη : η ≤ 2 / 3) :
    ∃ x y, 0 ≤ x ∧ 0 ≤ y ∧ 0 < Qf κ N ηB x * Pf N η ηB x y := by
  obtain ⟨X, hX0, hX⟩ := Qf_eventually_sign (κ := κ) hN hB
  refine ⟨X, 1, hX0, zero_le_one, ?_⟩
  have hQ := hX X le_rfl
  have hbr : 0 < brk η ηB X 1 := by
    simp only [brk]
    have : 0 ≤ X * (η - ηB) := mul_nonneg hX0 (by linarith)
    linarith
  have e : Qf κ N ηB X * Pf N η ηB X 1 = (Qf κ N ηB X * N) * brk η ηB X 1 := by
    simp only [Pf]; ring
  rw [e]
  exact mul_pos hQ hbr

/-- **Bad curvature: no exact zero for `η ≠ 0`.** For `η_B > 0` and `η ≠ 0`, every finite
ground-state parameter `κ` leaves a phase-space point with a positive integrand. Inside the window
`η_B ≤ η ≤ 2/3` this is a failure of attainment only (`bad_curvature_window_not_attained`). -/
theorem bad_curvature_not_attained {κ N η ηB : ℝ} (hN : N ≠ 0) (hB : 0 < ηB) (hη : η ≠ 0) :
    ∃ x y, 0 ≤ x ∧ 0 ≤ y ∧ 0 < Qf κ N ηB x * Pf N η ηB x y := by
  rcases lt_or_gt_of_ne hη with h | h
  · exact unstable_of_eta_neg hN hB.ne' h
  · rcases lt_or_ge η ηB with h1 | h1
    · exact unstable_of_lt_etaB hN h h1
    · rcases le_or_gt η (2 / 3) with h2 | h2
      · exact bad_curvature_window_not_attained hN hB h1 h2
      · exact unstable_of_eta_gt hN hB.ne' h2

/-- **The bracket is nonnegative in the window** `0 ≤ η ≤ 2/3`, `η_B ≤ η`. -/
theorem brk_nonneg {η ηB x y : ℝ} (h0 : 0 ≤ η) (h1 : η ≤ 2 / 3) (hB : ηB ≤ η) (hx : 0 ≤ x)
    (hy : 0 ≤ y) : 0 ≤ brk η ηB x y := by
  simp only [brk]
  have : 0 ≤ η * y := mul_nonneg h0 hy
  have : 0 ≤ x * (η - ηB) := mul_nonneg hx (by linarith)
  linarith

/-- **Good curvature, stable window.** For `η_B ≤ 0`, `0 ≤ η ≤ 2/3` and `κ N ≤ 0`, the
integrand vanishes at every `(x, y)`. -/
theorem good_curvature_stable {κ N η ηB : ℝ} (hB : ηB ≤ 0) (h0 : 0 ≤ η) (h1 : η ≤ 2 / 3)
    (hκ : κ * N ≤ 0) : ∀ x y, 0 ≤ x → 0 ≤ y → Qf κ N ηB x * Pf N η ηB x y ≤ 0 := by
  intro x y hx hy
  have hb := brk_nonneg (ηB := ηB) h0 h1 (by linarith) hx hy
  have e : Qf κ N ηB x * Pf N η ηB x y = (κ * N + x * N ^ 2 * ηB) * brk η ηB x y := by
    simp only [Qf, Pf]; ring
  rw [e]
  have : x * N ^ 2 * ηB ≤ 0 := by
    have := mul_nonneg hx (sq_nonneg N)
    nlinarith
  exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hb

/-- **Good curvature: stable iff `0 ≤ η ≤ 2/3`** (agrees with the source). -/
theorem good_curvature_stable_iff {N η ηB : ℝ} (hN : N ≠ 0) (hB : ηB < 0) :
    (∃ κ, ∀ x y, 0 ≤ x → 0 ≤ y → Qf κ N ηB x * Pf N η ηB x y ≤ 0) ↔ 0 ≤ η ∧ η ≤ 2 / 3 := by
  constructor
  · rintro ⟨κ, hκ⟩
    by_contra h
    rcases not_and_or.1 h with h | h
    · obtain ⟨x, y, hx, hy, hpos⟩ := unstable_of_eta_neg (κ := κ) hN hB.ne (lt_of_not_ge h)
      linarith [hκ x y hx hy]
    · obtain ⟨x, y, hx, hy, hpos⟩ := unstable_of_eta_gt (κ := κ) hN hB.ne (lt_of_not_ge h)
      linarith [hκ x y hx hy]
  · rintro ⟨h0, h1⟩
    exact ⟨0, good_curvature_stable hB.le h0 h1 (by simp)⟩

/-- **The ground state for good curvature.** With `κ = −N`, `η_B ≤ 0`: `Q ≠ 0` and `Q P ≤ 0`
at every point, so the isodynamic ground state `G = |c|/|a|` reproduces `c` (`a G = c` with
`a = Δψ Q`, `c = −Δψ P`): the density constraint holds pointwise, hence after integration. -/
theorem good_curvature_ground_state {N η ηB Δψ : ℝ} (hN : N ≠ 0) (hΔ : Δψ ≠ 0) (hB : ηB ≤ 0)
    (h0 : 0 ≤ η) (h1 : η ≤ 2 / 3) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Δψ * Qf (-N) N ηB x * groundState (Δψ * Qf (-N) N ηB x) 0 (-(Δψ * Pf N η ηB x y)) 0 =
      -(Δψ * Pf N η ηB x y) := by
  set a := Δψ * Qf (-N) N ηB x with ha
  set c := -(Δψ * Pf N η ηB x y) with hc
  have hQN : Qf (-N) N ηB x * N < 0 := by
    have e : Qf (-N) N ηB x * N = -N ^ 2 + x * N ^ 2 * ηB := by simp only [Qf]; ring
    rw [e]
    have : x * N ^ 2 * ηB ≤ 0 := by
      have := mul_nonneg hx (sq_nonneg N)
      nlinarith
    have : 0 < N ^ 2 := by positivity
    linarith
  have ha0 : a ≠ 0 := by
    rw [ha]
    refine mul_ne_zero hΔ ?_
    intro h; rw [h, zero_mul] at hQN; exact lt_irrefl _ hQN
  have hac : 0 ≤ a * c := by
    have := good_curvature_stable (κ := -N) hB h0 h1 (by nlinarith [sq_nonneg N]) x y hx hy
    have e : a * c = -(Δψ ^ 2 * (Qf (-N) N ηB x * Pf N η ηB x y)) := by
      rw [ha, hc]; ring
    rw [e]
    have : 0 ≤ Δψ ^ 2 := sq_nonneg _
    nlinarith
  unfold groundState
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
  rw [Real.sqrt_div' _ (sq_nonneg a), Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs]
  rcases lt_or_gt_of_ne ha0 with h | h
  · have hc' : c ≤ 0 := by nlinarith
    rw [abs_of_neg h, abs_of_nonpos hc']
    field_simp
  · have hc' : 0 ≤ c := by nlinarith
    rw [abs_of_pos h, abs_of_nonneg hc']
    field_simp

/-- **`η = 0` is stable for every `η_B`**: `κ = −N` gives `Q P = −N²(1 − x η_B)² ≤ 0`. So the
source's "η ≥ η_B is necessary" fails at `η = 0` when `η_B > 0`. -/
theorem eta_zero_stable (N ηB : ℝ) :
    ∀ x y, Qf (-N) N ηB x * Pf N 0 ηB x y ≤ 0 := by
  intro x y
  have e : Qf (-N) N ηB x * Pf N 0 ηB x y = -(N ^ 2 * (1 - x * ηB) ^ 2) := by
    simp only [Qf, Pf, brk]; ring
  rw [e]
  have := mul_nonneg (sq_nonneg N) (sq_nonneg (1 - x * ηB))
  linarith

end PlasmaLean.Kinetic.ITGAE
