/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Tactic.LinearCombination

/-!
# The derivative of a family of invariant tori in the KAM frame (conditional part)

Note N-48 §11, question Q-36, claims C1/C2. If invariant tori `K_s` form a differentiable family
with frequencies `ω_s`, differentiating the invariance equation and writing
`∂_s K = ξ₁ ∂_θK + ξ₂ N` in the KAM frame `(∂_θK, N)` gives the **linearized frame equations**
(the triangular form that defines the torsion `T`, as in the Newton step of
`Design/KamFlowStepG`: `ξ₂ = −½ coh(η₂) + c̄`, `ξ₁ = −½ coh(η₁ + Tξ₂)`):

* normal: `𝓛 ξ₂ = 0`,
* tangential: `𝓛 ξ₁ + T ξ₂ = ω′` (the frequency change, a constant),

with `𝓛` the derivative along the frequency. This file proves what follows from these
equations **alone**, in an abstract algebra of functions on the torus: averaging `avg` with
`avg 1 = 1`, `avg ∘ 𝓛 = 0`, and `ker 𝓛 = constants` (the role of the Diophantine condition):

* `normal_part_const`: `ξ₂` is a constant;
* `frequency_derivative` (**twist = rate of frequency change per unit normal displacement**):
  `ω′ = ⟨T⟩ · ξ₂`;
* `normal_displacement`: if `⟨T⟩ ≠ 0`, `ξ₂ = ω′/⟨T⟩` (claim C2 of N-48: the normal part of the
  derivative is `⟨T⟩⁻¹` per unit frequency);
* `tangential_unique`: `ξ₁` is unique up to an additive constant (the phase gauge `⟨a⟩`);
* fixtures: `trivialFrame` (accepted: one point, `𝓛 = 0`), `no_family_of_zero_twist`
  (rejected: with `⟨T⟩ = 0` there is no family with `ω′ ≠ 0`).

With the normal frame vector normalized to sweep unit flux (the project frame, density
`D/R⁷ = R B^φ`, N-48 §8), `ξ₂ = dΦ/ds` up to the `2π` of the angle units, so
`frequency_derivative` reads `⟨T⟩ = dω/dΦ`, i.e. **twist = shear**.

**What is not proved here (the remaining gap).** That the tori near a certified one form a
differentiable (Whitney-C¹ on the Diophantine set) family whose derivative satisfies the
linearized frame equations; and an instance of `FrameData` on the strip algebra `FA` (the
statement `ker 𝓛 = constants` for Diophantine frequencies, from `Theory/KAM/Cohomological`).
-/

public section

namespace PlasmaLean.Theory.KAM.Family

variable {𝕜 E : Type*} [Field 𝕜] [CommRing E] [Algebra 𝕜 E]

/-- **Frame data on a torus algebra**: an average with `avg 1 = 1`, and the derivative along the
frequency `𝓛`, with `avg ∘ 𝓛 = 0` and kernel the constants. -/
structure FrameData (𝕜 E : Type*) [Field 𝕜] [CommRing E] [Algebra 𝕜 E] where
  /-- The torus average. -/
  avg : E →ₗ[𝕜] 𝕜
  /-- The derivative along the frequency vector. -/
  L : E →ₗ[𝕜] E
  /-- `⟨1⟩ = 1`. -/
  avg_one : avg 1 = 1
  /-- Derivatives have zero average. -/
  avg_L : ∀ u, avg (L u) = 0
  /-- The kernel of `𝓛` is the constants (Diophantine/ergodic frequency). -/
  ker_L : ∀ u, L u = 0 → u = algebraMap 𝕜 E (avg u)

namespace FrameData

variable (D : FrameData 𝕜 E)

/-- The average of a constant. -/
theorem avg_algebraMap (c : 𝕜) : D.avg (algebraMap 𝕜 E c) = c := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, D.avg_one, smul_eq_mul, mul_one]

/-- **The normal part is constant.** -/
theorem normal_part_const {ξ₂ : E} (hn : D.L ξ₂ = 0) : ξ₂ = algebraMap 𝕜 E (D.avg ξ₂) :=
  D.ker_L ξ₂ hn

/-- **Twist = rate of frequency change per unit normal displacement**: from the linearized frame
equations, `ω′ = ⟨T⟩ · ξ₂`. -/
theorem frequency_derivative {T ξ₁ ξ₂ : E} {ω' : 𝕜} (hn : D.L ξ₂ = 0)
    (ht : D.L ξ₁ + T * ξ₂ = algebraMap 𝕜 E ω') : ω' = D.avg T * D.avg ξ₂ := by
  have h := congrArg D.avg ht
  rw [map_add, D.avg_L, zero_add, D.avg_algebraMap, D.normal_part_const hn,
    Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, map_smul, smul_eq_mul] at h
  rw [← h, mul_comm]

/-- **The normal displacement is `ω′/⟨T⟩`** when the twist is nondegenerate. -/
theorem normal_displacement {T ξ₁ ξ₂ : E} {ω' : 𝕜} (hT : D.avg T ≠ 0) (hn : D.L ξ₂ = 0)
    (ht : D.L ξ₁ + T * ξ₂ = algebraMap 𝕜 E ω') : ξ₂ = algebraMap 𝕜 E (ω' / D.avg T) := by
  rw [D.normal_part_const hn, D.frequency_derivative hn ht, mul_div_cancel_left₀ _ hT]

/-- **The tangential part is unique up to a constant** (the phase gauge). -/
theorem tangential_unique {T ξ₁ ξ₁' ξ₂ : E} {ω' : 𝕜}
    (ht : D.L ξ₁ + T * ξ₂ = algebraMap 𝕜 E ω') (ht' : D.L ξ₁' + T * ξ₂ = algebraMap 𝕜 E ω') :
    ξ₁ - ξ₁' = algebraMap 𝕜 E (D.avg (ξ₁ - ξ₁')) := by
  apply D.ker_L
  rw [map_sub]
  linear_combination ht - ht'

/-- **Rejected fixture.** With zero average twist, no family has a nonzero frequency change. -/
theorem no_family_of_zero_twist {T ξ₁ ξ₂ : E} {ω' : 𝕜} (hT : D.avg T = 0) (hω : ω' ≠ 0)
    (hn : D.L ξ₂ = 0) : D.L ξ₁ + T * ξ₂ ≠ algebraMap 𝕜 E ω' := by
  intro ht
  exact hω (by rw [D.frequency_derivative hn ht, hT, zero_mul])

end FrameData

/-- **Accepted fixture (degenerate torus: one point).** `E = 𝕜`, `avg = id`, `𝓛 = 0`. -/
def trivialFrame : FrameData 𝕜 𝕜 where
  avg := LinearMap.id
  L := 0
  avg_one := rfl
  avg_L := fun _ => rfl
  ker_L := fun _ _ => rfl

/-- On the trivial frame, the normal displacement is `ω′/T`. -/
theorem trivialFrame_displacement {T ξ₁ ξ₂ ω' : 𝕜} (hT : T ≠ 0) (ht : 0 + T * ξ₂ = ω') :
    ξ₂ = ω' / T := by
  have h : (trivialFrame (𝕜 := 𝕜)).L ξ₁ + T * ξ₂ = algebraMap 𝕜 𝕜 ω' := by
    simpa [trivialFrame] using ht
  have := (trivialFrame (𝕜 := 𝕜)).normal_displacement hT rfl h
  simpa [trivialFrame] using this

end PlasmaLean.Theory.KAM.Family
