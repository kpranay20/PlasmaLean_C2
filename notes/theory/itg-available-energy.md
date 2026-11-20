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
| Produces | `Theory/Kinetic/ITGAvailableEnergy.lean`, `Theory/Kinetic/ITGBoozer.lean`, `Theory/Kinetic/ITGStabilityWindows.lean`, `Theory/Kinetic/ITGDriftIdentity.lean`, `Theory/Kinetic/ITGDriftChart.lean`; Q-35 (d) |
| Difficulty | routine (algebra); moderate (η windows, Boozer link); hard (certified evaluation on the Dommaschk tori) |
| Status | algebra, Boozer link and isodynamic stability windows **verified** (20 November 2026; zero warnings, standard axioms); evaluation on a candidate open (blocked like C2: no volume chart) |
| Lean evidence | `aeIntegrand_nonneg`, `aeIntegrand_eq_zero_iff`, `aeIntegrand_pos_of_antiparallel`, `itgIntegrand_eq_zero_iff`, `aeIntegrand_isodynamic`, `aeIntegrand_smul`, `aeFormula_nonneg`, `aeFormula_eq_zero_of`, `groundState_constraints_flat`, `itg_ae_zero_of_no_temperature_gradient`; Boozer link: `hasDerivAt_logB_alpha`, `hasDerivAt_logB_psi`, `omegaPsi_eq_zero_of_Btheta`, `omegaPsi_ne_zero`, `boozerIntegrand_isodynamic`, `paper_condition_not_sufficient`; windows: `good_curvature_stable_iff`, `good_curvature_ground_state`, `bad_curvature_not_attained`, `eta_zero_stable`, `Qf_eventually_sign`; drift identity: `boozer_drift_identity`, `chart_drift_alpha`, `chart_drift_psi` (default build) |
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
coordinate along the line; **now verified** (`Theory/Kinetic/ITGDriftIdentity`,
`ITGDriftChart`): at a `Contract.BoozerChart` point, for `v·eᵢ = ∂ᵢ|B|` and `A·eᵢ = ∂ᵢf`,
`(B × v)·A = |B|²(b₁c₂ − b₂c₁)`; hence `(B × ∇|B|)·∇α = |B|²(∂_ψB + ι′φ∂_θB)` and
`(B × ∇|B|)·∇ψ = −|B|²∂_θB` (Cramer expansion plus `G = J|B|²`; the chain rule for `∇|B|` and the
coordinate gradients are supplied). **Physics:** `omegaPsi_ne_zero` shows that exact quasi-axisymmetry
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
| bad curvature `η_B > 0`, `η ≠ 0` | every **finite** `κ` leaves a positive integrand (`bad_curvature_not_attained`); inside `η_B ≤ η ≤ 2/3` this is non-attainment only (see below); outside it the instability is genuine | stable for `0 ≤ η ≤ 2/3`, `η ≥ max η_B`: **correct as an infimum** |
| `η = 0`, any `η_B` | stable (`eta_zero_stable`) | "η ≥ η_B is necessary" fails at `η = 0` |

**Bad curvature: an attainment subtlety, not an error (corrected 20 November 2026).** The source's
eqs. 2.36–2.39 show a ground state needs `σ(κ_α + ω_α) = −σ(ω*^T − ω_α)` everywhere when
`ω*^T − ω_α` has a fixed sign; `κ_α + ω_α = κ + μB₀∂_ψ ln B` eventually has the wrong sign when
`η_B > 0` (`Qf_eventually_sign`), so (2.36) has no exact solution. A first version of this note
called this a gap in the source's result. An independent numerical check reversed that verdict.

**Independent check (20 November 2026).** Transcription choices checked verbatim against the PDF:
`ω_α ≡ μB₀(∂ln B/∂ψ)_{α,ℓ}` (2.8b); the constraint (2.17a) and `G` (2.15) as used; the velocity
domain "V : (μ ⩾ 0, v∥ ∈ R, ℓ ∈ R)" (p. 8); "κψ and κα only depend on ℓ" (p. 10);
`η_B = (∂ ln B/∂ψ)/(d ln n/dψ)` (p. 10); good curvature "∂ψ B|α,ℓ = v∇·∇α > 0" with
"∂ψ ln n < 0" (p. 11). A pure-Python solution of (2.15), (2.17a), (2.21) written directly in
`(μ, v∥)`, with `B = 1.1 ≠ B₀ = 1` (so the `B ≈ B₀` of eq. 2.29 plays no role), `d ln n/dψ = −1`
(script in the session scratchpad, not in the repo; untrusted numerics):

- good curvature (`∂_ψ ln B = +0.3`, `η = 0.5`): every `κ > 0` solves (2.17a) with `A = 0`
  (the degenerate family of the source's footnote 6);
- bad curvature (`∂_ψ ln B = −0.3`, `η = 0.5 ≥ η_B = 0.3`): no exact root, but the residual and
  `A` decay like `e^{−κB/(B₀|∂_ψ ln B|)}`: `A/scale = 3.2·10⁻², 1.3·10⁻⁶, 9.7·10⁻¹³, 5.9·10⁻¹⁹` at
  `κ = 1, 4, 8, 12`, reaching machine zero;
- bad curvature, `η = 0`: the source's `κ = −ω*` (eq. 2.27) gives residual `0` and `A = 0`.

So the source's bad-curvature stability window is right with `A = 0` read as an infimum,
approached as `κ_α → ∞`. What remains is a technical remark (the ground state is not attained),
not an error. A Lean proof of `A(κ) → 0` would need the integrated formula (open).

All statements are pointwise in `(x, y)`; with a positive Maxwellian weight and continuous
integrand, "integrand zero everywhere" is equivalent to `A = 0` for a given `κ`.

## 7. Next steps (Q-35)

- (c′) done (drift identity on a Boozer chart); remaining: derive `v·eᵢ = ∂ᵢ|B|` from `modB` and the coordinate gradients from a differentiable inverse chart.
- (d) Evaluation on a candidate: route (i) or (ii) of §5 first.
- The integrated (measure-theoretic) form of the windows, and a proof that `A(κ) → 0` as
  `κ → ∞` in the bad-curvature window.
