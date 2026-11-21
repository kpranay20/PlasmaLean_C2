/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.ITGShear
public import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Irrational field lines meet both signs of `∂_θ B` arbitrarily far out

Note N-48 §10, question Q-36. `Theory/Kinetic/ITGShear` needs two points of a field line, beyond
any given length, where `∂_θ B ≥ c` and `∂_θ B ≤ −c`. This file proves that they exist.

## Results

* `exists_tail_near` (**tail density**): if `a/p` is irrational (`p > 0`), then for every
  target `x`, tolerance `ε > 0` and `N`, some `n ≥ N` and `k : ℤ` have `|n a + k p − x| < ε`.
  Proof: density of `ℤa + ℤp` (`dense_addSubgroupClosure_pair_iff`) gives a positive multiple
  with a nonzero residue `d`, `|d| < ε`; stepping from `N` by that multiple moves the residue by
  `d` each time and reaches the target (`walk`).
* `exists_deriv_neg_of_periodic`, `exists_deriv_pos_of_periodic`: the derivative of a periodic
  differentiable function that is positive somewhere is negative somewhere (and conversely):
  otherwise the function is monotone and periodic, hence constant.
* `line_two_points`: a function `g(θ, φ)`, `p`-periodic in `θ`, `P`-periodic in `φ`, continuous
  in `θ` at `φ = φ₀` and taking both signs there, takes values `≥ c` and `≤ −c` on the line
  `θ = α + ιφ` beyond every length, if `ιP/p` is irrational.
* `boozer_two_points`: for a `BoozerField` periodic in `θ` and `φ` on the surface `ψ > 0`, with
  `∂_θ B` continuous in `θ` and **not identically zero** on the section `φ = φ₀` (the field is
  not isodynamic there), and `ιP/p` irrational: there is `c > 0` such that every field line
  `α` has, beyond every length, points with `∂_θ B ≥ c` and with `∂_θ B ≤ −c`.
* `boozer_bad_curvature_of_shear`: combined with `ITGShear.boozer_bad_curvature`, a sheared
  (`|ι′| ≥ s₀ > 0`), non-isodynamic, irrational surface has points of curvature
  `∂_ψ ln B|_{α,φ} < −K` on every field line, for every `K ≥ 0`, given global bounds
  `|∂_ψ B| ≤ M`, `0 < B ≤ B_max` on the surface.

The periodicity of `∂_θ B` is derived from that of `B` (uniqueness of derivatives).

**Not covered.** Certified values of `M`, `B_max` and of the section where `∂_θ B ≠ 0` for the
Dommaschk candidate (they need chart data, Q-35 (d)); the shear lower bound is the certified
twist, subject to the twist = shear identification (N-48 §8).
-/

public section
noncomputable section

namespace PlasmaLean.Kinetic.ITGAE

open Set PlasmaLean.Kinetic.Boozer

/-! ## Tail density of an irrational rotation -/

/-- **One step of the walk.** If `t/d ≥ 0` and `d ≠ 0`, some `j : ℕ` has `|t − j d| < |d|`. -/
theorem walk {t d : ℝ} (hd : d ≠ 0) (ht : 0 ≤ t / d) : ∃ j : ℕ, |t - j * d| < |d| := by
  refine ⟨⌊t / d⌋₊, ?_⟩
  have h1 := Nat.floor_le ht
  have h2 := Nat.lt_floor_add_one (t / d)
  have e : t - (⌊t / d⌋₊ : ℝ) * d = d * (t / d - ⌊t / d⌋₊) := by field_simp
  rw [e, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ t / d - ⌊t / d⌋₊)]
  have hdpos : 0 < |d| := abs_pos.2 hd
  nlinarith

/-- **A positive multiple with a small nonzero residue.** If `a/p` is irrational and `p > 0`,
for every `0 < ε ≤ p` some `m > 0` and `k : ℤ` give `d = m a + k p` with `0 < |d| < ε`. -/
theorem exists_small_residue {a p ε : ℝ} (hp : 0 < p) (hirr : Irrational (a / p))
    (hε : 0 < ε) (hεp : ε ≤ p) :
    ∃ m : ℕ, 0 < m ∧ ∃ k : ℤ, 0 < |m * a + k * p| ∧ |m * a + k * p| < ε := by
  have hd := dense_addSubgroupClosure_pair_iff.2 hirr
  obtain ⟨z, hz, hz1, hz2⟩ := hd.exists_between hε
  rw [SetLike.mem_coe, AddSubgroup.mem_closure_pair] at hz
  obtain ⟨m, n, rfl⟩ := hz
  simp only [zsmul_eq_mul] at hz1 hz2
  have hm : m ≠ 0 := by
    rintro rfl
    simp only [Int.cast_zero, zero_mul, zero_add] at hz1 hz2
    have h1 : (0 : ℝ) < n := by
      by_contra h; push Not at h; nlinarith
    have h2 : (n : ℝ) < 1 := by
      by_contra h; push Not at h; nlinarith
    have : (0 : ℤ) < n := by exact_mod_cast h1
    have : n < 1 := by exact_mod_cast h2
    omega
  rcases lt_or_gt_of_ne hm with hneg | hpos
  · refine ⟨(-m).toNat, by omega, -n, ?_⟩
    have e : (((-m).toNat : ℕ) : ℝ) = -(m : ℝ) := by
      have : (((-m).toNat : ℕ) : ℤ) = -m := Int.toNat_of_nonneg (by omega)
      exact_mod_cast this
    rw [e, Int.cast_neg]
    have e2 : -(m : ℝ) * a + -(n : ℝ) * p = -((m : ℝ) * a + n * p) := by ring
    rw [e2, abs_neg, abs_of_pos hz1]
    exact ⟨hz1, hz2⟩
  · refine ⟨m.toNat, by omega, n, ?_⟩
    have e : ((m.toNat : ℕ) : ℝ) = (m : ℝ) := by
      have : ((m.toNat : ℕ) : ℤ) = m := Int.toNat_of_nonneg (by omega)
      exact_mod_cast this
    rw [e, abs_of_pos hz1]
    exact ⟨hz1, hz2⟩

/-- **Tail density.** If `a/p` is irrational and `p > 0`, then for every `x`, `ε > 0` and `N`
there are `n ≥ N` and `k : ℤ` with `|n a + k p − x| < ε`. -/
theorem exists_tail_near {a p : ℝ} (hp : 0 < p) (hirr : Irrational (a / p)) (x : ℝ) {ε : ℝ}
    (hε : 0 < ε) (N : ℕ) : ∃ n : ℕ, N ≤ n ∧ ∃ k : ℤ, |n * a + k * p - x| < ε := by
  obtain ⟨m, hm, k₁, hd0, hdε⟩ :=
    exists_small_residue hp hirr (lt_min hε hp) (min_le_right ε p)
  set d := (m : ℝ) * a + k₁ * p with hd
  have hdne : d ≠ 0 := abs_pos.1 hd0
  -- choose `k₀` so that `t = x − N a − k₀ p` has the sign of `d`
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℤ, 0 ≤ (x - N * a - k₀ * p) / d := by
    rcases lt_or_gt_of_ne hdne with hneg | hpos
    · refine ⟨⌈(x - N * a) / p⌉, div_nonneg_of_nonpos ?_ hneg.le⟩
      have := Int.le_ceil ((x - N * a) / p)
      rw [div_le_iff₀ hp] at this
      linarith
    · refine ⟨⌊(x - N * a) / p⌋, div_nonneg ?_ hpos.le⟩
      have := Int.floor_le ((x - N * a) / p)
      rw [le_div_iff₀ hp] at this
      linarith
  obtain ⟨j, hj⟩ := walk hdne hk₀
  refine ⟨N + j * m, by omega, k₀ + j * k₁, ?_⟩
  have e : ((N + j * m : ℕ) : ℝ) * a + ((k₀ + j * k₁ : ℤ) : ℝ) * p - x =
      -((x - N * a - k₀ * p) - j * d) := by
    rw [hd]; push_cast; ring
  rw [e, abs_neg]
  exact hj.trans (hdε.trans_le (min_le_left ε p))

/-! ## Periodic functions: the derivative takes both signs -/

/-- **A periodic function whose derivative is positive somewhere has a derivative negative
somewhere.** (Otherwise it is monotone and periodic, hence constant.) -/
theorem exists_deriv_neg_of_periodic {f f' : ℝ → ℝ} {p : ℝ} (hp : 0 < p)
    (hper : ∀ θ, f (θ + p) = f θ) (hd : ∀ θ, HasDerivAt f (f' θ) θ) {θ₀ : ℝ}
    (hpos : 0 < f' θ₀) : ∃ θ, f' θ < 0 := by
  by_contra h
  push Not at h
  have hdiff : Differentiable ℝ f := fun θ => (hd θ).differentiableAt
  have hmono : Monotone f :=
    monotone_of_deriv_nonneg hdiff fun θ => by rw [(hd θ).deriv]; exact h θ
  have hper' : Function.Periodic f p := hper
  have hconst : ∀ x y, f x = f y := by
    have key : ∀ x y, f x ≤ f y := by
      intro x y
      obtain ⟨n, hn⟩ := exists_nat_gt ((x - y) / p)
      have : x ≤ y + n * p := by
        rw [div_lt_iff₀ hp] at hn; linarith
      calc f x ≤ f (y + n * p) := hmono this
        _ = f y := hper'.nat_mul n y
    exact fun x y => le_antisymm (key x y) (key y x)
  have h0 : HasDerivAt f 0 θ₀ := by
    have : f = fun _ => f θ₀ := funext fun x => hconst x θ₀
    rw [this]; exact hasDerivAt_const _ _
  have := (hd θ₀).unique h0
  linarith

/-- The mirror statement: negative somewhere ⇒ positive somewhere. -/
theorem exists_deriv_pos_of_periodic {f f' : ℝ → ℝ} {p : ℝ} (hp : 0 < p)
    (hper : ∀ θ, f (θ + p) = f θ) (hd : ∀ θ, HasDerivAt f (f' θ) θ) {θ₀ : ℝ}
    (hneg : f' θ₀ < 0) : ∃ θ, 0 < f' θ := by
  obtain ⟨θ, hθ⟩ := exists_deriv_neg_of_periodic (f := fun x => -f x) (f' := fun x => -f' x) hp
    (fun θ => by simp [hper θ]) (fun θ => (hd θ).neg) (θ₀ := θ₀) (by linarith)
  exact ⟨θ, by linarith⟩

/-! ## Both signs on an irrational line -/

/-- **Values near a target along the line, beyond any length.** -/
theorem line_near {g : ℝ → ℝ → ℝ} {p P α ι φ₀ θ₀ ε : ℝ} (hp : 0 < p) (hP : 0 < P)
    (hθ : ∀ θ φ, g (θ + p) φ = g θ φ) (hφ : ∀ θ φ, g θ (φ + P) = g θ φ)
    (hirr : Irrational (ι * P / p)) (hε : 0 < ε) (L : ℝ) :
    ∃ φ, L < φ ∧ ∃ θ, |θ - θ₀| < ε ∧ g (α + ι * φ) φ = g θ φ₀ := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((L - φ₀) / P)
  obtain ⟨n, hn, k, hk⟩ := exists_tail_near hp hirr (θ₀ - α - ι * φ₀) hε N
  refine ⟨φ₀ + n * P, ?_, α + ι * (φ₀ + n * P) + k * p, ?_, ?_⟩
  · have : (N : ℝ) ≤ n := by exact_mod_cast hn
    rw [div_lt_iff₀ hP] at hN
    nlinarith
  · have e : α + ι * (φ₀ + n * P) + k * p - θ₀ = n * (ι * P) + k * p - (θ₀ - α - ι * φ₀) := by
      ring
    rw [e]; exact hk
  · have h1 : Function.Periodic (fun θ => g θ (φ₀ + n * P)) p := fun θ => hθ θ _
    have h2 : Function.Periodic (fun φ => g (α + ι * (φ₀ + n * P)) φ) P :=
      fun φ => hφ _ φ
    calc g (α + ι * (φ₀ + n * P)) (φ₀ + n * P)
        = g (α + ι * (φ₀ + n * P) + k * p) (φ₀ + n * P) := (h1.int_mul k _).symm
      _ = g (α + ι * (φ₀ + n * P) + k * p) φ₀ := by
          have h3 : Function.Periodic (fun φ => g (α + ι * (φ₀ + n * P) + k * p) φ) P :=
            fun φ => hφ _ φ
          have := h3.nat_mul n φ₀
          simpa [add_comm] using this

/-- **Both signs along an irrational line.** If `g` is periodic, continuous in `θ` at `φ₀`,
and `g(θ₊, φ₀) > c`, `g(θ₋, φ₀) < −c`, then beyond every length the line `θ = α + ιφ` has
points with `g ≥ c` and with `g ≤ −c`. -/
theorem line_two_points {g : ℝ → ℝ → ℝ} {p P α ι φ₀ θp θm c : ℝ} (hp : 0 < p) (hP : 0 < P)
    (hθ : ∀ θ φ, g (θ + p) φ = g θ φ) (hφ : ∀ θ φ, g θ (φ + P) = g θ φ)
    (hirr : Irrational (ι * P / p)) (hcont : Continuous fun θ => g θ φ₀)
    (hplus : c < g θp φ₀) (hminus : g θm φ₀ < -c) (L : ℝ) :
    ∃ φ₁ φ₂, L < φ₁ ∧ L < φ₂ ∧ c ≤ g (α + ι * φ₁) φ₁ ∧ g (α + ι * φ₂) φ₂ ≤ -c := by
  have nb : ∀ θ₀ : ℝ, ∀ U : Set ℝ, IsOpen U → g θ₀ φ₀ ∈ U →
      ∃ ε > 0, ∀ θ, |θ - θ₀| < ε → g θ φ₀ ∈ U := by
    intro θ₀ U hU hmem
    have := hcont.continuousAt (x := θ₀) |>.preimage_mem_nhds (hU.mem_nhds hmem)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 this
    exact ⟨ε, hε, fun θ hθ' => hball (by simpa [Real.dist_eq] using hθ')⟩
  obtain ⟨ε₁, hε₁, h₁⟩ := nb θp (Ioi c) isOpen_Ioi hplus
  obtain ⟨ε₂, hε₂, h₂⟩ := nb θm (Iio (-c)) isOpen_Iio hminus
  obtain ⟨φ₁, hL₁, θ₁, hθ₁, e₁⟩ := line_near (α := α) (θ₀ := θp) hp hP hθ hφ hirr hε₁ L
  obtain ⟨φ₂, hL₂, θ₂, hθ₂, e₂⟩ := line_near (α := α) (θ₀ := θm) hp hP hθ hφ hirr hε₂ L
  refine ⟨φ₁, φ₂, hL₁, hL₂, ?_, ?_⟩
  · rw [e₁]; exact (h₁ θ₁ hθ₁).le
  · rw [e₂]; exact (h₂ θ₂ hθ₂).le

/-! ## On the Boozer model -/

/-- `∂_θ B` is the `θ`-derivative of `B` on the surface `ψ > 0`. -/
theorem hasDerivAt_B_theta (F : BoozerField) {ψ φ : ℝ} (hψ : 0 < ψ) (θ : ℝ) :
    HasDerivAt (fun t => F.B ψ t φ) (F.Bθ ψ θ φ) θ := by
  have hc : HasDerivAt (fun t : ℝ => (ψ, t, φ)) ((0 : ℝ), (1 : ℝ), (0 : ℝ)) θ :=
    (hasDerivAt_const θ ψ).prodMk ((hasDerivAt_id θ).prodMk (hasDerivAt_const θ φ))
  have h := (F.hasFDerivAt_B (ψ, θ, φ) hψ).comp_hasDerivAt θ hc
  simpa [Function.comp_def, gradCLM_apply] using h

/-- **Two points with `∂_θ B ≥ c` and `≤ −c` on every field line, beyond every length.** For a
Boozer field periodic in `θ` (period `p`) and `φ` (period `P`) on the surface `ψ > 0`, with
`∂_θ B` continuous in `θ` on the section `φ₀` and nonzero somewhere there, and `ιP/p`
irrational. -/
theorem boozer_two_points (F : BoozerField) {ψ p P φ₀ θ₀ : ℝ} (hψ : 0 < ψ) (hp : 0 < p)
    (hP : 0 < P) (hθ : ∀ θ φ, F.B ψ (θ + p) φ = F.B ψ θ φ)
    (hφ : ∀ θ φ, F.B ψ θ (φ + P) = F.B ψ θ φ) (hirr : Irrational (F.ι ψ * P / p))
    (hcont : Continuous fun θ => F.Bθ ψ θ φ₀) (hne : F.Bθ ψ θ₀ φ₀ ≠ 0) :
    ∃ c > 0, ∀ α L : ℝ, ∃ φ₁ φ₂, L < φ₁ ∧ L < φ₂ ∧
      c ≤ F.Bθ ψ (thetaOf F ψ α φ₁) φ₁ ∧ F.Bθ ψ (thetaOf F ψ α φ₂) φ₂ ≤ -c := by
  -- periodicity of `∂_θ B`, from that of `B`
  have hθ' : ∀ θ φ, F.Bθ ψ (θ + p) φ = F.Bθ ψ θ φ := by
    intro θ φ
    have h1 := (hasDerivAt_B_theta F (φ := φ) hψ (θ + p)).comp_add_const θ p
    have h2 := hasDerivAt_B_theta F (φ := φ) hψ θ
    have e : (fun t => F.B ψ (t + p) φ) = fun t => F.B ψ t φ := funext fun t => hθ t φ
    rw [e] at h1
    exact h1.unique h2
  have hφ' : ∀ θ φ, F.Bθ ψ θ (φ + P) = F.Bθ ψ θ φ := by
    intro θ φ
    have h1 := hasDerivAt_B_theta F (φ := φ + P) hψ θ
    have h2 := hasDerivAt_B_theta F (φ := φ) hψ θ
    have e : (fun t => F.B ψ t (φ + P)) = fun t => F.B ψ t φ := funext fun t => hφ t φ
    rw [e] at h1
    exact h1.unique h2
  -- both signs on the section
  have hper : ∀ θ, F.B ψ (θ + p) φ₀ = F.B ψ θ φ₀ := fun θ => hθ θ φ₀
  have hd : ∀ θ, HasDerivAt (fun t => F.B ψ t φ₀) (F.Bθ ψ θ φ₀) θ :=
    hasDerivAt_B_theta F hψ
  obtain ⟨θp, hp'⟩ : ∃ θ, 0 < F.Bθ ψ θ φ₀ := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact exists_deriv_pos_of_periodic hp hper hd h
    · exact ⟨θ₀, h⟩
  obtain ⟨θm, hm'⟩ := exists_deriv_neg_of_periodic hp hper hd hp'
  set c := min (F.Bθ ψ θp φ₀) (-F.Bθ ψ θm φ₀) / 2 with hc
  have hc0 : 0 < c := by rw [hc]; exact half_pos (lt_min hp' (by linarith))
  refine ⟨c, hc0, fun α L => ?_⟩
  have hplus : c < F.Bθ ψ θp φ₀ := by
    have := min_le_left (F.Bθ ψ θp φ₀) (-F.Bθ ψ θm φ₀); rw [hc]; linarith
  have hminus : F.Bθ ψ θm φ₀ < -c := by
    have := min_le_right (F.Bθ ψ θp φ₀) (-F.Bθ ψ θm φ₀); rw [hc]; linarith
  obtain ⟨φ₁, φ₂, h1, h2, h3, h4⟩ := line_two_points (g := fun θ φ => F.Bθ ψ θ φ) (α := α)
    hp hP hθ' hφ' hirr hcont hplus hminus L
  exact ⟨φ₁, φ₂, h1, h2, h3, h4⟩

/-- **Every field line of a sheared, non-isodynamic, irrational surface has arbitrarily bad
curvature.** Under the hypotheses of `boozer_two_points`, with `|ι′| ≥ s₀ > 0` and global bounds
`|∂_ψ B| ≤ M`, `0 < B ≤ B_max` on the surface: for every `K ≥ 0` and every field line `α`,
some point has `∂_ψ ln B|_{α,φ} < −K`. -/
theorem boozer_bad_curvature_of_shear (F : BoozerField) (dι : ℝ → ℝ)
    {ψ p P φ₀ θ₀ s₀ M Bmax : ℝ} (hψ : 0 < ψ) (hp : 0 < p) (hP : 0 < P)
    (hθ : ∀ θ φ, F.B ψ (θ + p) φ = F.B ψ θ φ) (hφ : ∀ θ φ, F.B ψ θ (φ + P) = F.B ψ θ φ)
    (hirr : Irrational (F.ι ψ * P / p)) (hcont : Continuous fun θ => F.Bθ ψ θ φ₀)
    (hne : F.Bθ ψ θ₀ φ₀ ≠ 0) (hs : 0 < s₀) (hι : s₀ ≤ |dι ψ|) (hBmax : 0 < Bmax)
    (hB : ∀ θ φ, 0 < F.B ψ θ φ ∧ F.B ψ θ φ ≤ Bmax) (hM : ∀ θ φ, |F.Bψ ψ θ φ| ≤ M)
    {K : ℝ} (hK : 0 ≤ K) (α : ℝ) : ∃ φ, dPsiLogB F dι ψ α φ < -K := by
  obtain ⟨c, hc, hall⟩ := boozer_two_points F hψ hp hP hθ hφ hirr hcont hne
  obtain ⟨φ₁, φ₂, h1, h2, h3, h4⟩ := hall α ((M + K * Bmax) / (s₀ * c))
  rcases boozer_bad_curvature F dι hs hι hc hK hBmax (hB _ _).1 (hB _ _).2 (hB _ _).1
    (hB _ _).2 (hM _ _) (hM _ _) h1 h2 h3 h4 with h | h
  · exact ⟨φ₁, h⟩
  · exact ⟨φ₂, h⟩

end PlasmaLean.Kinetic.ITGAE
