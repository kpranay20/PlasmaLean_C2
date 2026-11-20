# Available energy of the curvature-driven ITG instability

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-47` |
| Title | Available energy of the curvature-driven ITG instability: source check, verified algebra, and the route to a certified value on a candidate |
| Kind | source synthesis / formalization |
| Addresses | `Q-35` (new); `Q-33` (d), `G-10`, `G-2` |
| Depends on | N-45 §4 (source triage), N-20 (TEM available-energy kernel), N-46 (gyrokinetic contract); Lean: none (Mathlib only) |
| Dependency requirement | the AE formula is supplied by the source (variational derivation not formalized) |
| Produces | `Theory/Kinetic/ITGAvailableEnergy.lean`, `Theory/Kinetic/ITGBoozer.lean`, `Theory/Kinetic/ITGStabilityWindows.lean`; Q-35 (d) |
| Difficulty | routine (algebra); moderate (η windows, Boozer link); hard (certified evaluation on the Dommaschk tori) |
| Status | algebra, Boozer link and isodynamic stability windows **verified** (20 November 2026; zero warnings, standard axioms); evaluation on a candidate open (blocked like C2: no volume chart) |
| Lean evidence | `aeIntegrand_nonneg`, `aeIntegrand_eq_zero_iff`, `aeIntegrand_pos_of_antiparallel`, `itgIntegrand_eq_zero_iff`, `aeIntegrand_isodynamic`, `aeIntegrand_smul`, `aeFormula_nonneg`, `aeFormula_eq_zero_of`, `groundState_constraints_flat`, `itg_ae_zero_of_no_temperature_gradient`; Boozer link: `hasDerivAt_logB_alpha`, `hasDerivAt_logB_psi`, `omegaPsi_eq_zero_of_Btheta`, `omegaPsi_ne_zero`, `boozerIntegrand_isodynamic`, `paper_condition_not_sufficient`; windows: `good_curvature_stable_iff`, `good_curvature_ground_state`, `bad_curvature_unstable`, `eta_zero_stable`, `Qf_eventually_sign` (default build) |
| Audit evidence | not audited |
| Last updated | 20 November 2026: created |

## Purpose and scope

The energetic growth bound of N-46 does not see the geometry (`growth_bound_indep_A`), so it cannot
rank candidates. The available energy (AE) of the curvature-driven ITG mode can: it is an integral
along the flux tube of the `∇B` drifts `ω_α = μB₀ ∂_ψ ln B|_{α,ℓ}` and
`ω_ψ = −μB₀ ∂_α ln B|_{ψ,ℓ}`, which are functions of the field. This note records the source, the
corrections found, and the verified algebra.

**Source.** R. Mackenbach, P. Helander, M. Landreman, S. Brunner, J. Proll, *On the
curvature-driven ion-temperature-gradient instability and its available energy*, J. Plasma Phys.
(2025), open access. Model: flux tube, collisionless, electrostatic, adiabatic electrons, parallel
dynamics neglected, fixed density profile, local Maxwellian, unit-disk correlation domain.

## 1. The formula (supplied)

`A = C ∫ (f_M/T₀) [√(a²+b²)√(c²+d²) − ac − bd] dℓ dμ dv∥`, with `a = Δψ(ω_α + κ_α)`,
`b = Δα(ω_ψ − κ_ψ)`, `c = Δψ(ω_α − ω*^T)`, `d = Δα ω_ψ` (source eq. 2.21), ground state
`G = √((c²+d²)/(a²+b²))` and constraints `∫ w a G = ∫ w c`, `∫ w b G = ∫ w d` at each `ℓ`
(eq. 2.17 rewritten; `w = f_M/T₀`).

## 2. Source check (20 November 2026, verbatim from the published PDF, J. Plasma Phys. 91 (2025) E144)

1. **Vanishing condition: misstated, partly self-corrected.** §2.3, p. 9: "In the notation of
   (2.22), this occurs if and only if ad = bc". This is false as stated: the integrand vanishes iff
   `ad = bc` **and** `ac + bd ≥ 0` (`aeIntegrand_eq_zero_iff`; counterexample
   `aeIntegrand_pos_of_antiparallel`; physical form `paper_condition_not_sufficient`). The authors
   themselves note two paragraphs later (p. 10): "simply satisfying (2.23) is not sufficient for
   having zero available energy, and more care is required", and they treat the isodynamic case
   with the ramp function `R`, which is exactly the missing sign condition. Their derived results
   survive: they use `ad = bc` only as a necessary condition (eq. 2.24 and the two cases follow)
   and check sufficiency separately (G = 1 in §2.3.1, the sign of (2.29) in §2.3.2). So: a wrong
   "if and only if" sentence, not a wrong conclusion.
2. **"Positive definite".** p. 9: "the available energy is always positive definite". It is only
   nonnegative; the paper's own §2.3 finds `A = 0` cases. Their proof ("squaring both sides")
   also silently assumes `ac + bd ≥ 0`, though the case `ac + bd < 0` is trivial.
3. **Prefactor.** Eq. (2.3): `dr dv = (π/m) dψ dα dℓ dμ dv∥` with `μ = m v⊥²/2B` (p. 6). With that
   `μ`, `d³v = 2π v⊥ dv⊥ dv∥ = (2πB/m) dμ dv∥` and `d³r = dψ dα dℓ / B`, giving `2π/m`. A factor 2
   in the absolute normalization appears likely (it carries into the `π²ΔψΔα/(4m)` of eq. 2.21).
   It does not affect signs, vanishing sets or relative comparisons; the Lean formula keeps a
   general `C > 0`.
4. **Pure density gradient.** Eqs. 2.25–2.27 do follow from 2.23 (differentiate in `μ` with
   `∂_ε ω* = 0`, then substitute; the earlier doubt came from a garbled extraction). Typo: "Substituting
   (2.28) into (2.15)" should read (2.27). The conclusion `A = 0` is also proved directly
   (`itg_ae_zero_of_no_temperature_gradient`).
5. Footnote 4 (p. 10) confirms `η ≥ η_B` is stated as necessary, with the residual AE small.

## 3. Verified results

`Theory/Kinetic/ITGAvailableEnergy.lean`, namespace `PlasmaLean.Kinetic.ITGAE`: nonnegativity
(Cauchy–Schwarz through the Lagrange identity), the corrected vanishing condition, the
isodynamic reduction `2(−ac)₊` (eq. 2.28), scaling (`A → t⁴A` with the prefactor), the
integrated formula's nonnegativity, and the `η = 0` fixture.

**Physics remark.** Because parallel dynamics is neglected, `ω_ψ` is the *local* radial `∇B`
drift, not its bounce average. Omnigeneity (C2) does not make it vanish; only an isodynamic field
(`B = B(ψ)` on the tube) does. So this AE measures something C2 does not, which is why it belongs
in the turbulence part of the contract and not as a restatement of C2.

## 4. The Boozer link (verified, Q-35 (c))

`Theory/Kinetic/ITGBoozer.lean`: field-line coordinates `(ψ, α = θ − ιφ, φ)` on the vacuum Boozer
model; `∂_α ln B|_{ψ,φ} = ∂_θB/B` and `∂_ψ ln B|_{α,φ} = (∂_ψB + ι′φ∂_θB)/B` proved as derivatives
(`hasDerivAt_logB_alpha`, `hasDerivAt_logB_psi`, `ι′` a supplied derivative); the drifts
`omegaAlpha`, `omegaPsi` and the integrand `boozerIntegrand`. Hand calculation (not in Lean):
in vacuum Boozer form `v_∇·∇α = ∂_ψB|_{α,φ}` and `v_∇·∇ψ = −∂_θB` exactly, so `φ` is the right
coordinate along the line. **Physics:** `omegaPsi_ne_zero` shows that exact quasi-axisymmetry
(`∂_θB ≠ 0`) leaves the local radial drift, so C2 does not imply a small ITG available energy;
only isodynamic tubes remove it (`boozerIntegrand_isodynamic`).

## 5. Obstacle for a candidate (raised 20 November 2026)

The Dommaschk candidate has two certified invariant tori and no Boozer chart over a volume
(audit AC-1), the same gap that blocks C2. What a single certified torus does and does not give:

- `ω_ψ ∝ (b × ∇B)·∇ψ`: computable on one torus up to the factor `|∇ψ|`: `b × ∇B` from the
  explicit field, `∇ψ/|∇ψ|` the torus normal. `|∇ψ|` along the line needs the neighbouring
  surface spacing. Since `a, b, c, d` all carry it, it rescales the integrand at each `ℓ`
  (`aeIntegrand_smul`), but it varies with `ℓ`, so it is not a harmless constant.
- `ω_α ∝ (b × ∇B)·∇α`: the in-surface part of `∇α` comes from the torus angles; the normal part
  needs `ι′` (shear) and the normal derivative of the angle map, i.e. information off the torus.

Routes, both shared with the open C2 problem: (i) an approximate Boozer chart on a thin shell
around a certified torus with a certified defect (the README's first priority for C2); (ii) the
Whitney-smooth KAM family: the a-posteriori KAM data (twist, the derivative of the torus with
respect to its frequency) give `ι′` and the normal structure to first order, which is all the
linearized flux tube of the source uses. Solving (i) or (ii) once serves C2 and the ITG AE
together.

## 6. Stability windows in isodynamic tubes (verified, Q-35 (b))

`Theory/Kinetic/ITGStabilityWindows.lean`, per point `ℓ`, normalized `x = μB₀/T₀`,
`y = m v∥²/2T₀`, `N = T₀ d ln n/dψ ≠ 0`: `ω*^T − ω_α = N[1 − 3η/2 + ηy + x(η − η_B)]` (source eq.
2.29) and `κ_α + ω_α = κ + xNη_B`; the integrand is `2Δψ²(QP)₊` (`itg_window_eq`).

| Regime | Result | Source (§2.3.2) |
| --- | --- | --- |
| good curvature `η_B < 0` | stable (some `κ` zeroes the integrand everywhere) **iff** `0 ≤ η ≤ 2/3` (`good_curvature_stable_iff`); `κ = −N` satisfies the ground-state constraint pointwise (`good_curvature_ground_state`) | agrees |
| bad curvature `η_B > 0`, `η ≠ 0` | **never** stable: every `κ` leaves a point with positive integrand (`bad_curvature_unstable`) | claims stability for `0 ≤ η ≤ 2/3`, `η ≥ max η_B` |
| `η = 0`, any `η_B` | stable (`eta_zero_stable`) | "η ≥ η_B necessary" fails at `η = 0` |

**The bad-curvature gap.** The source's sufficiency argument (eqs. 2.36–2.39) correctly shows that
a ground state must satisfy `σ(κ_α + ω_α) = −σ(ω*^T − ω_α)` everywhere when `ω*^T − ω_α` has a
fixed sign. But `κ_α + ω_α = κ + xNη_B` is affine in `x = μB₀/T₀ ∈ [0, ∞)` with slope of the sign
of `Nη_B`, so for `η_B > 0` it eventually has the sign of `N`, which is the sign of
`ω*^T − ω_α` (`Qf_eventually_sign`). Hence the isodynamic density constraint (2.36) has **no
solution** in that regime, and the formula (2.21) never gives `A = 0`. Whether the true available
energy (a supremum over admissible rearrangements, here possibly approached as `κ → ∓∞`) is zero
is a separate question that the source's framework does not settle. Consequences: the corollary
after eq. 2.35 ("increase the ITG to satisfy it", stability with bad curvature balanced by
`|∂_ψ ln T|`) is unsupported as stated; the source's figure 1 is drawn for `∂_ψ ln B > 0` (good
curvature for a peaked density), where the result stands. With a peaked density
(`d ln n/dψ < 0`), `η_B > 0` means `∂_ψ B|_{α,ℓ} < 0`, i.e. bad curvature.

All statements are pointwise in `(x, y)`; with a positive Maxwellian weight and continuous
integrand, "integrand zero everywhere" is equivalent to `A = 0`.

## 7. Next steps (Q-35)

- (c′) The drift identity `v_∇·∇α = ∂_ψB|_{α,φ}` from `Contract.BoozerChart`.
- (d) Evaluation on a candidate: route (i) or (ii) of §5 first.
- The integrated (measure-theoretic) form of the windows, and the infimum question for bad
  curvature.
