/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.LinearGyrokinetic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Lp.Matrix
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# A discretized instance of the linear gyrokinetic model contract

Note N-46, question Q-34 (b). The contract `LinearGKModel` (`Theory/Kinetic/LinearGyrokinetic`)
assumes that streaming and drift conserve the free energy (`skew`) and that the gyroaverage maps
are adjoint (`adj`). Here both are **proved** for a concrete finite-dimensional discretization, so
the contract is satisfiable by an actual operator and its theorems (free-energy balance,
Helander–Plunk growth bound) apply to it.

## Construction

* **Matrix models** (`MatrixGKData`): any skew-Hermitian matrix `A` (`Aᴴ = −A`), any matrix `J`
  with `K = Jᴴ`, any drive matrix `Ω` and `λ > 0` give a `LinearGKModel` on Euclidean spaces
  (`MatrixGKData.toModel`). `skew` and `adj` follow from
  `Matrix.toEuclideanLin_conjTranspose_eq_adjoint`.
* **The grid** (`gridData`): field-line points `i : Fin n` (periodic, spacing `h`) and velocity
  nodes `a : Fin m`; the unknown is `g (i, a)` in the rescaled variable
  `√(w_a T/F₀(a)) g_phys`, so that the free-energy inner product is the Euclidean one
  (`w_a` quadrature weights; `F₀` is taken independent of `l`, as in `(v∥, v⊥)` coordinates).
  - streaming: centred differences `v_a (g(i+1, a) − g(i−1, a))/(2h)` (`streamMat`);
  - magnetic drift: `i ω_d(i, a) g(i, a)` with real `ω_d` (`driftMat`): **the geometry**;
  - gyroaverage: `(J φ)(i, a) = j(i, a) φ(i)`, `(K g)(i) = Σ_a j(i, a) g(i, a)`, with real
    `j(i, a) = e J₀(k⊥(i) ρ_a) √(w_a F₀(a)/T)`;
  - drive: `(Ω φ)(i, a) = ω*^T(a) j(i, a) φ(i)`.

## Results

* `streamMat_skewH`, `driftMat_skewH`: the streaming and drift matrices are skew-Hermitian.
* `gridModel`: the grid is a `LinearGKModel` (contract clauses proved).
* `gridModel_K_apply`, `gridModel_qn_bound`: `‖K g‖² ≤ c λ ‖g‖²` whenever
  `Σ_a j(i, a)² ≤ c λ` for every `i` (discrete Cauchy–Schwarz). With
  `Σ_a j(i, a)² ≈ (n e²/T) Γ₀(b_i)` this is `c = Γ₀/(1+τ) < 1`, so `growth_le_of_qn` applies.
* `gridModel_no_drive`: with `ω*^T = 0` no eigenmode grows or decays.
* Rejected fixture `not_skew_one`: an operator with numerical dissipation (here the identity, the
  simplest damping term) violates `skew`, so upwind-type discretizations are not instances.

**Not covered.** Convergence of the grid to the continuum operator (Q-34 (c)); `l`-dependent
`F₀`; ballooning (non-periodic) boundary conditions; the values of `ω_d`, `k⊥` from a certified
field (Q-34 (d)).
-/

public section
noncomputable section

namespace PlasmaLean.Kinetic.Gyrokinetic

open scoped InnerProductSpace ComplexConjugate
open Matrix

/-! ## Matrix models -/

section MatrixModel

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- A skew-Hermitian matrix conserves the Euclidean energy: `re ⟪x, A x⟫ = 0`. -/
theorem re_inner_toEuclideanLin_self_eq_zero {A : Matrix ι ι ℂ} (hA : Aᴴ = -A)
    (x : EuclideanSpace ℂ ι) : (⟪x, A.toEuclideanLin x⟫_ℂ).re = 0 := by
  have h1 : ⟪x, A.toEuclideanLin x⟫_ℂ = ⟪Aᴴ.toEuclideanLin x, x⟫_ℂ := by
    rw [toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_left]
  have h2 : ⟪A.toEuclideanLin x, x⟫_ℂ = conj ⟪x, A.toEuclideanLin x⟫_ℂ :=
    (inner_conj_symm _ _).symm
  rw [hA, map_neg, LinearMap.neg_apply, inner_neg_left, h2] at h1
  have := congrArg Complex.re h1
  rw [Complex.neg_re, Complex.conj_re] at this
  linarith

/-- **Data of a matrix gyrokinetic model**: a skew-Hermitian streaming-and-drift matrix `Am`, a
gyroaverage matrix `Jm` (with `K = Jmᴴ`), a drive matrix `Ωm` and `λ > 0`. -/
structure MatrixGKData (ι κ : Type*) [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] where
  /-- Streaming and drift. -/
  Am : Matrix ι ι ℂ
  /-- Gyroaverage `J`. -/
  Jm : Matrix ι κ ℂ
  /-- Gradient drive `Ω`. -/
  Ωm : Matrix ι κ ℂ
  /-- `λ`. -/
  lam : ℝ
  /-- `λ > 0`. -/
  lam_pos : 0 < lam
  /-- Streaming and drift are skew-Hermitian. -/
  skewH : Amᴴ = -Am

/-- **A matrix model satisfies the gyrokinetic contract.** -/
@[expose] def MatrixGKData.toModel (d : MatrixGKData ι κ) :
    LinearGKModel (EuclideanSpace ℂ ι) (EuclideanSpace ℂ κ) where
  A := d.Am.toEuclideanLin
  J := LinearMap.toContinuousLinearMap d.Jm.toEuclideanLin
  K := LinearMap.toContinuousLinearMap d.Jmᴴ.toEuclideanLin
  Ω := d.Ωm.toEuclideanLin
  lam := d.lam
  lam_pos := d.lam_pos
  adj := by
    intro g u
    simp only [LinearMap.coe_toContinuousLinearMap']
    rw [toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_left]
  skew := re_inner_toEuclideanLin_self_eq_zero d.skewH

/-- **Rejected fixture.** Damping (the identity matrix, the prototype of numerical dissipation)
does not conserve the free energy. -/
theorem not_skew_one [Nonempty ι] :
    ¬ ∀ x : EuclideanSpace ℂ ι, (⟪x, (1 : Matrix ι ι ℂ).toEuclideanLin x⟫_ℂ).re = 0 := by
  intro h
  obtain ⟨i⟩ := ‹Nonempty ι›
  have := h (EuclideanSpace.single i 1)
  simp at this

end MatrixModel

/-! ## The grid -/

section Grid

variable {n m : ℕ} [NeZero n]

/-- Centred-difference streaming on a periodic field-line grid of spacing `h`:
`(S g)(i, a) = v_a (g(i+1, a) − g(i−1, a))/(2h)`. -/
@[expose] def streamMat (v : Fin m → ℝ) (h : ℝ) : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ :=
  fun p q => if p.2 = q.2 then
    ((v p.2 / (2 * h) : ℝ) : ℂ) *
      ((if q.1 = p.1 + 1 then 1 else 0) - (if q.1 = p.1 - 1 then 1 else 0))
    else 0

/-- The magnetic drift `i ω_d(i, a)` (a diagonal matrix, `ω_d` real). -/
@[expose] def driftMat (ωd : Fin n → Fin m → ℝ) : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ :=
  diagonal fun p => Complex.I * (ωd p.1 p.2 : ℂ)

/-- Centred streaming is skew-Hermitian. -/
theorem streamMat_skewH (v : Fin m → ℝ) (h : ℝ) :
    (streamMat (n := n) v h)ᴴ = -(streamMat v h) := by
  ext p q
  rw [conjTranspose_apply, Matrix.neg_apply]
  simp only [streamMat]
  have e1 : (p.1 = q.1 + 1) ↔ (q.1 = p.1 - 1) := by rw [eq_sub_iff_add_eq]; exact eq_comm
  have e2 : (p.1 = q.1 - 1) ↔ (q.1 = p.1 + 1) := by rw [eq_sub_iff_add_eq]; exact eq_comm
  by_cases hpq : p.2 = q.2
  · simp only [hpq, ↓reduceIte, e1, e2]
    split_ifs <;> simp [Complex.conj_ofReal]
  · simp [hpq, Ne.symm hpq]

omit [NeZero n] in
/-- The drift `i ω_d` is skew-Hermitian. -/
theorem driftMat_skewH (ωd : Fin n → Fin m → ℝ) : (driftMat ωd)ᴴ = -(driftMat ωd) := by
  ext p q
  rw [conjTranspose_apply, Matrix.neg_apply]
  simp only [driftMat, diagonal_apply]
  by_cases hpq : p = q
  · subst hpq
    simp [Complex.conj_ofReal]
  · simp [hpq, Ne.symm hpq]

/-- The gyroaverage matrix `(J φ)(i, a) = j(i, a) φ(i)`. -/
@[expose] def gyroMat (j : Fin n → Fin m → ℝ) : Matrix (Fin n × Fin m) (Fin n) ℂ :=
  fun p i => if p.1 = i then (j p.1 p.2 : ℂ) else 0

/-- The drive matrix `(Ω φ)(i, a) = ω*^T(a) j(i, a) φ(i)`. -/
@[expose] def driveMat (j : Fin n → Fin m → ℝ) (ωT : Fin m → ℝ) :
    Matrix (Fin n × Fin m) (Fin n) ℂ :=
  fun p i => if p.1 = i then ((ωT p.2 * j p.1 p.2 : ℝ) : ℂ) else 0

/-- **The grid model data**: streaming with velocities `v` and spacing `h`, drift `ω_d`,
gyroaverage weights `j`, drive `ω*^T`, and `λ > 0`. -/
@[expose] def gridData (v : Fin m → ℝ) (h : ℝ) (ωd : Fin n → Fin m → ℝ)
    (j : Fin n → Fin m → ℝ) (ωT : Fin m → ℝ) (lam : ℝ) (hlam : 0 < lam) :
    MatrixGKData (Fin n × Fin m) (Fin n) where
  Am := streamMat v h + driftMat ωd
  Jm := gyroMat j
  Ωm := driveMat j ωT
  lam := lam
  lam_pos := hlam
  skewH := by rw [conjTranspose_add, streamMat_skewH, driftMat_skewH, neg_add]

/-- **The discretized gyrokinetic model** (a `LinearGKModel` with `skew` and `adj` proved). -/
@[expose] def gridModel (v : Fin m → ℝ) (h : ℝ) (ωd : Fin n → Fin m → ℝ)
    (j : Fin n → Fin m → ℝ) (ωT : Fin m → ℝ) (lam : ℝ) (hlam : 0 < lam) :
    LinearGKModel (EuclideanSpace ℂ (Fin n × Fin m)) (EuclideanSpace ℂ (Fin n)) :=
  (gridData v h ωd j ωT lam hlam).toModel

variable {v : Fin m → ℝ} {h : ℝ} {ωd : Fin n → Fin m → ℝ} {j : Fin n → Fin m → ℝ}
  {ωT : Fin m → ℝ} {lam : ℝ} {hlam : 0 < lam}

/-- The gyroaveraged density on the grid: `(K g)(i) = Σ_a j(i, a) g(i, a)`. -/
theorem gridModel_K_apply (g : EuclideanSpace ℂ (Fin n × Fin m)) (i : Fin n) :
    (gridModel v h ωd j ωT lam hlam).K g i = ∑ a, (j i a : ℂ) * g (i, a) := by
  simp only [gridModel, gridData, MatrixGKData.toModel, LinearMap.coe_toContinuousLinearMap',
    toLpLin_apply, PiLp.toLp_apply, mulVec, dotProduct, conjTranspose_apply, gyroMat,
    Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i]
  · simp [Complex.conj_ofReal]
  · intro b _ hb
    simp [hb]
  · simp

/-- **Quasineutrality bound on the grid** (discrete Cauchy–Schwarz): if
`Σ_a j(i, a)² ≤ c λ` for every `i`, then `‖K g‖² ≤ c λ ‖g‖²`. -/
theorem gridModel_qn_bound {c : ℝ} (hc : ∀ i, ∑ a, j i a ^ 2 ≤ c * lam)
    (g : EuclideanSpace ℂ (Fin n × Fin m)) :
    ‖(gridModel v h ωd j ωT lam hlam).K g‖ ^ 2 ≤ c * lam * ‖g‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [gridModel_K_apply]
  have h1 : ‖∑ a, (j i a : ℂ) * g (i, a)‖ ≤ ∑ a, |j i a| * ‖g (i, a)‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    congr 1
    funext a
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun a => |j i a|)
    (fun a => ‖g (i, a)‖)
  simp only [sq_abs] at h2
  have h3 : 0 ≤ ∑ a, ‖g (i, a)‖ ^ 2 := Finset.sum_nonneg (fun _ _ => by positivity)
  have h4 : 0 ≤ ∑ a, |j i a| * ‖g (i, a)‖ := Finset.sum_nonneg (fun _ _ => by positivity)
  calc ‖∑ a, (j i a : ℂ) * g (i, a)‖ ^ 2 ≤ (∑ a, |j i a| * ‖g (i, a)‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (∑ a, j i a ^ 2) * ∑ a, ‖g (i, a)‖ ^ 2 := h2
    _ ≤ c * lam * ∑ a, ‖g (i, a)‖ ^ 2 := mul_le_mul_of_nonneg_right (hc i) h3

/-- **Growth bound on the grid.** With `Σ_a j(i, a)² ≤ c λ`, `c < 1`, and `D ≤ Λ H`, every
nonzero eigenmode of the discretized model has `re s ≤ Λ`. -/
theorem gridModel_growth_le {c Λ : ℝ} (hc1 : c < 1) (hc : ∀ i, ∑ a, j i a ^ 2 ≤ c * lam)
    (hΛ : ∀ g, (gridModel v h ωd j ωT lam hlam).D g ≤ Λ * (gridModel v h ωd j ωT lam hlam).H g)
    {s : ℂ} {g : EuclideanSpace ℂ (Fin n × Fin m)}
    (hs : (gridModel v h ωd j ωT lam hlam).IsEigenmode s g) (hg : g ≠ 0) : s.re ≤ Λ :=
  LinearGKModel.growth_le_of_qn _ hΛ hc1 (gridModel_qn_bound hc) hs hg

/-- **No drive on the grid.** With `ω*^T = 0`, every eigenmode with positive free energy has
`re s = 0`. -/
theorem gridModel_no_drive {s : ℂ} {g : EuclideanSpace ℂ (Fin n × Fin m)}
    (hs : (gridModel v h ωd j (fun _ => 0) lam hlam).IsEigenmode s g)
    (hH : 0 < (gridModel v h ωd j (fun _ => 0) lam hlam).H g) : s.re = 0 := by
  refine LinearGKModel.eigen_re_eq_zero_of_no_drive _ ?_ hs hH
  have : driveMat j (fun _ : Fin m => (0 : ℝ)) = 0 := by
    ext p i
    simp [driveMat]
  simp only [gridModel, gridData, MatrixGKData.toModel, this, map_zero]

end Grid

end PlasmaLean.Kinetic.Gyrokinetic
