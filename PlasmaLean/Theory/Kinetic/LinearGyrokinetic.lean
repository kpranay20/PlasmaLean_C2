/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Linear local electrostatic gyrokinetics: model contract, free energy and growth bounds

Note N-46 (`notes/theory/gyrokinetic-model-contract.md`), question Q-34; layer 2 of the
turbulence programme (N-45). Model commitment approved by the user, 20 November 2026.

## Model

One Fourier mode `k⊥ = k_ψ ∇ψ + k_α ∇α` of the linear, collisionless, electrostatic gyrokinetic
equation in a flux tube, kinetic ions and adiabatic (Boltzmann) electrons
(Helander & Plunk, J. Plasma Phys. 88 (2022) 905880207, eqs. as restated in Podavini et al.,
Part 5, eqs. 2.1–2.7):

`∂ₜ g + v∥ ∂_l g + i ω_d g = (e F₀/T) J₀ (∂ₜ φ + i ω*^T φ)`,
`λ φ = e ∫ J₀ g d³v`, `λ = n e²/T_i + n e²/T_e`.

It is written abstractly as operators between complex inner-product spaces:

* `V`: the space of the nonadiabatic ion distribution `g(l, v)` with the free-energy inner
  product `⟪g, h⟫ = ⟨∫ T conj(g) h / F₀ d³v⟩` (`⟨·⟩` the field-line average);
* `U`: the space of potentials `φ(l)` with `⟪φ, ψ⟫ = ⟨conj(φ) ψ⟩`;
* `A g = v∥ ∂_l g + i ω_d g`: parallel streaming and the magnetic drift: **the geometry**;
* `J φ = e J₀ F₀ φ / T` and its adjoint `K g = e ∫ J₀ g d³v` (`adj`);
* `Ω φ = ω*^T e J₀ F₀ φ / T`: the gradient drive (`ω*^T = ω* [1 + η(v²/v_th² − 3/2)]`).

Then the equation is `ġ + A g = J φ̇ + i Ω φ` with `φ = λ⁻¹ K g`.

**The contract clause `skew`:** `re ⟪g, A g⟫ = 0`. Streaming and drift conserve free energy.
For the physical operators this is integration by parts along `l` (ballooning decay or
periodicity) and the reality of `ω_d`; it is a supplied property of the instance, stated once here.

## Results

* `eigen_balance`: for an eigenmode `g e^{st}`, `(re s) · H g = D g`, with the free energy
  `H g = ‖g‖² − λ ‖φ‖²` and the drive `D g = re ⟪g, i Ω φ⟫`;
* `H_ge`: positivity, `H g ≥ (1 − c) ‖g‖²` when `‖K g‖² ≤ c λ ‖g‖²` (physically
  `c = Γ₀(b)/(1+τ) ≤ 1/(1+τ) < 1`);
* `growth_le`: if `D ≤ Λ H` on all of `V` then every eigenmode with `g ≠ 0` has `re s ≤ Λ`
  (the Helander–Plunk bound `γ ≤ max D/H`);
* `growth_bound_indep_A`: `H` and `D` do not involve `A`, so the bound is the same for every
  geometry operator: the energetic bound cannot discriminate between geometries except through
  `K` (that is, through `k⊥ρ`);
* `eigen_re_eq_zero_of_no_drive`: no gradients (`Ω = 0`) ⇒ no growing or damped eigenmode;
* `energy_balance`: along any solution, `d/dt H(g(t)) = 2 D(g(t))`.

**Not covered.** The concrete operators (velocity integrals, Bessel `J₀`, the ballooning
domain); the proof of `skew` for them; kinetic electrons, electromagnetic terms, collisions
(collisions only decrease `H`); nonlinear saturation (out of reach; N-45 §Purpose).
-/

public section
noncomputable section

namespace PlasmaLean.Kinetic.Gyrokinetic

open scoped InnerProductSpace ComplexConjugate

/-- **Linear local electrostatic gyrokinetic model** (one Fourier mode, kinetic ions, adiabatic
electrons), in operator form. See the module documentation. -/
structure LinearGKModel (V U : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup U] [InnerProductSpace ℂ U] where
  /-- Parallel streaming and magnetic drift, `g ↦ v∥ ∂_l g + i ω_d g`: the geometry. -/
  A : V →ₗ[ℂ] V
  /-- `J φ = e J₀ F₀ φ / T`. -/
  J : U →L[ℂ] V
  /-- `K g = e ∫ J₀ g d³v`, the gyroaveraged charge density. -/
  K : V →L[ℂ] U
  /-- `Ω φ = ω*^T e J₀ F₀ φ / T`, the gradient drive. -/
  Ω : U →ₗ[ℂ] V
  /-- `λ = n e²/T_i + n e²/T_e` (ion polarization-free part plus adiabatic electrons). -/
  lam : ℝ
  /-- `λ > 0`. -/
  lam_pos : 0 < lam
  /-- `J` and `K` are adjoint. -/
  adj : ∀ (g : V) (u : U), ⟪g, J u⟫_ℂ = ⟪K g, u⟫_ℂ
  /-- Streaming and drift conserve the free energy. -/
  skew : ∀ g : V, (⟪g, A g⟫_ℂ).re = 0

namespace LinearGKModel

variable {V U : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup U] [InnerProductSpace ℂ U] (M : LinearGKModel V U)

/-- The potential from quasineutrality, `φ = λ⁻¹ K g`. -/
@[expose] def phi (g : V) : U := ((M.lam : ℂ)⁻¹) • M.K g

/-- The free energy `H g = ‖g‖² − λ ‖φ‖²`. -/
@[expose] def H (g : V) : ℝ := ‖g‖ ^ 2 - M.lam * ‖M.phi g‖ ^ 2

/-- The gradient drive `D g = re ⟪g, i Ω φ⟫`. -/
@[expose] def D (g : V) : ℝ := (⟪g, Complex.I • M.Ω (M.phi g)⟫_ℂ).re

/-- `g e^{s t}` solves the equation: `s g + A g = J φ(s g) + i Ω φ(g)`. -/
@[expose] def IsEigenmode (s : ℂ) (g : V) : Prop :=
  s • g + M.A g = M.J (M.phi (s • g)) + Complex.I • M.Ω (M.phi g)

/-! ## Algebraic identities -/

/-- `φ` is linear: `φ(s g) = s φ(g)`. -/
theorem phi_smul (s : ℂ) (g : V) : M.phi (s • g) = s • M.phi g := by
  simp only [phi, map_smul]
  rw [smul_comm]

/-- `λ ‖φ‖² = ‖K g‖²/λ`. -/
theorem lam_mul_norm_phi_sq (g : V) : M.lam * ‖M.phi g‖ ^ 2 = ‖M.K g‖ ^ 2 / M.lam := by
  have hl := M.lam_pos
  simp only [phi, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hl]
  field_simp

/-- `H g = ‖g‖² − ‖K g‖²/λ`. -/
theorem H_eq (g : V) : M.H g = ‖g‖ ^ 2 - ‖M.K g‖ ^ 2 / M.lam := by
  rw [H, lam_mul_norm_phi_sq]

/-- `re ⟪x, s x⟫ = (re s) ‖x‖²`. -/
theorem re_inner_smul_self (s : ℂ) (x : V) : (⟪x, s • x⟫_ℂ).re = s.re * ‖x‖ ^ 2 := by
  rw [inner_smul_right, inner_self_eq_norm_sq_to_K]
  simp [Complex.mul_re, ← Complex.ofReal_pow]

/-- The quasineutral part: `re ⟪g, J φ(h)⟫ = re ⟪K g, K h⟫ / λ`. -/
theorem re_inner_J_phi (g h : V) :
    (⟪g, M.J (M.phi h)⟫_ℂ).re = (⟪M.K g, M.K h⟫_ℂ).re / M.lam := by
  rw [M.adj, phi, inner_smul_right]
  have : ((M.lam : ℂ)⁻¹) = ((M.lam⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  rw [this, Complex.re_ofReal_mul]
  field_simp

/-! ## Eigenmodes: the energy balance and the growth bound -/

/-- **Eigenmode energy balance.** `(re s) · H g = D g`. -/
theorem eigen_balance {s : ℂ} {g : V} (h : M.IsEigenmode s g) : s.re * M.H g = M.D g := by
  have e := congrArg (fun v => (⟪g, v⟫_ℂ).re) h
  simp only [inner_add_right, Complex.add_re, M.skew, add_zero] at e
  rw [re_inner_smul_self, re_inner_J_phi, map_smul, inner_smul_right] at e
  have hk : (s * ⟪M.K g, M.K g⟫_ℂ).re = s.re * ‖M.K g‖ ^ 2 := by
    rw [← inner_smul_right]
    exact re_inner_smul_self s _
  rw [hk] at e
  rw [H_eq, D, mul_sub, e]
  ring

/-- **Positivity of the free energy.** If `‖K g‖² ≤ c λ ‖g‖²` then `H g ≥ (1 − c) ‖g‖²`. -/
theorem H_ge {c : ℝ} (hc : ∀ g : V, ‖M.K g‖ ^ 2 ≤ c * M.lam * ‖g‖ ^ 2) (g : V) :
    (1 - c) * ‖g‖ ^ 2 ≤ M.H g := by
  rw [H_eq]
  have hl := M.lam_pos
  have : ‖M.K g‖ ^ 2 / M.lam ≤ c * ‖g‖ ^ 2 := by
    rw [div_le_iff₀ hl]
    nlinarith [hc g]
  nlinarith

/-- **Growth bound** (Helander–Plunk). If `D ≤ Λ H` everywhere, an eigenmode with `H g > 0`
grows at most at rate `Λ`. -/
theorem growth_le {Λ : ℝ} (hΛ : ∀ g : V, M.D g ≤ Λ * M.H g) {s : ℂ} {g : V}
    (h : M.IsEigenmode s g) (hH : 0 < M.H g) : s.re ≤ Λ := by
  have := M.eigen_balance h
  have h2 := hΛ g
  rw [← this] at h2
  exact le_of_mul_le_mul_right h2 hH

/-- Growth bound with positivity supplied by the quasineutrality bound `c < 1`. -/
theorem growth_le_of_qn {Λ c : ℝ} (hΛ : ∀ g : V, M.D g ≤ Λ * M.H g) (hc1 : c < 1)
    (hc : ∀ g : V, ‖M.K g‖ ^ 2 ≤ c * M.lam * ‖g‖ ^ 2) {s : ℂ} {g : V}
    (h : M.IsEigenmode s g) (hg : g ≠ 0) : s.re ≤ Λ := by
  refine M.growth_le hΛ h ?_
  have h1 := M.H_ge hc g
  have h2 : 0 < ‖g‖ ^ 2 := by positivity
  nlinarith

/-- **No gradients, no growth.** With `Ω = 0`, every eigenmode with `H g > 0` has `re s = 0`. -/
theorem eigen_re_eq_zero_of_no_drive (hΩ : M.Ω = 0) {s : ℂ} {g : V}
    (h : M.IsEigenmode s g) (hH : 0 < M.H g) : s.re = 0 := by
  have := M.eigen_balance h
  have hD : M.D g = 0 := by simp [D, hΩ]
  rw [hD] at this
  rcases mul_eq_zero.1 this with h1 | h1
  · exact h1
  · exact absurd h1 hH.ne'

/-- **Geometry independence of the energetic bound.** Replacing the streaming-and-drift operator
`A` by any other free-energy-conserving `A'` changes neither `H` nor `D`. -/
theorem growth_bound_indep_A (A' : V →ₗ[ℂ] V) (hA' : ∀ g : V, (⟪g, A' g⟫_ℂ).re = 0) :
    ({ M with A := A', skew := hA' } : LinearGKModel V U).H = M.H ∧
      ({ M with A := A', skew := hA' } : LinearGKModel V U).D = M.D :=
  ⟨rfl, rfl⟩

/-! ## The time-dependent energy balance -/

/-- **Free-energy balance.** Along a solution `ġ + A g = J φ̇ + i Ω φ`,
`d/dt H(g(t)) = 2 D(g(t))`. -/
theorem energy_balance {g g' : ℝ → V} {t : ℝ} (hg : HasDerivAt g (g' t) t)
    (heq : g' t + M.A (g t) = M.J (M.phi (g' t)) + Complex.I • M.Ω (M.phi (g t))) :
    HasDerivAt (fun τ => M.H (g τ)) (2 * M.D (g t)) t := by
  have hl := M.lam_pos.ne'
  -- derivatives of `re ⟪g, g⟫` and `re ⟪K g, K g⟫`
  have hK : HasDerivAt (fun τ => M.K (g τ)) (M.K (g' t)) t := by
    exact (M.K.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hg
  have d1 : HasDerivAt (fun τ => ⟪g τ, g τ⟫_ℂ) (⟪g t, g' t⟫_ℂ + ⟪g' t, g t⟫_ℂ) t :=
    hg.inner ℂ hg
  have d2 : HasDerivAt (fun τ => ⟪M.K (g τ), M.K (g τ)⟫_ℂ)
      (⟪M.K (g t), M.K (g' t)⟫_ℂ + ⟪M.K (g' t), M.K (g t)⟫_ℂ) t :=
    hK.inner ℂ hK
  have r1 : HasDerivAt (fun τ => (⟪g τ, g τ⟫_ℂ).re) ((⟪g t, g' t⟫_ℂ + ⟪g' t, g t⟫_ℂ).re) t :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt t d1
  have r2 : HasDerivAt (fun τ => (⟪M.K (g τ), M.K (g τ)⟫_ℂ).re)
      ((⟪M.K (g t), M.K (g' t)⟫_ℂ + ⟪M.K (g' t), M.K (g t)⟫_ℂ).re) t :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt t d2
  have hfun : (fun τ => M.H (g τ)) =
      fun τ => (⟪g τ, g τ⟫_ℂ).re - (⟪M.K (g τ), M.K (g τ)⟫_ℂ).re / M.lam := by
    funext τ
    rw [H_eq, ← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ)]
    rfl
  rw [hfun]
  refine (HasDerivAt.sub r1 (HasDerivAt.div_const r2 M.lam)).congr_deriv ?_
  -- the value of the derivative
  have e := congrArg (fun v => (⟪g t, v⟫_ℂ).re) heq
  simp only [inner_add_right, Complex.add_re, M.skew, add_zero, re_inner_J_phi] at e
  have c1 : (⟪g' t, g t⟫_ℂ).re = (⟪g t, g' t⟫_ℂ).re := by
    rw [← inner_conj_symm (g t) (g' t), Complex.conj_re]
  have c2 : (⟪M.K (g' t), M.K (g t)⟫_ℂ).re = (⟪M.K (g t), M.K (g' t)⟫_ℂ).re := by
    rw [← inner_conj_symm (M.K (g t)) (M.K (g' t)), Complex.conj_re]
  rw [Complex.add_re, Complex.add_re, c1, c2, e, D]
  ring

end LinearGKModel

end PlasmaLean.Kinetic.Gyrokinetic
