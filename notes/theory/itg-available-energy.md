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
| Produces | `Theory/Kinetic/ITGAvailableEnergy.lean`; Q-35 (b)–(d) |
| Difficulty | routine (algebra); moderate (η windows, Boozer link); hard (certified evaluation on the Dommaschk tori) |
| Status | algebra **verified** (20 November 2026; zero warnings, standard axioms); η windows, Boozer link and evaluation open |
| Lean evidence | `aeIntegrand_nonneg`, `aeIntegrand_eq_zero_iff`, `aeIntegrand_pos_of_antiparallel`, `itgIntegrand_eq_zero_iff`, `aeIntegrand_isodynamic`, `aeIntegrand_smul`, `aeFormula_nonneg`, `aeFormula_eq_zero_of`, `groundState_constraints_flat`, `itg_ae_zero_of_no_temperature_gradient` (default build) |
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

## 2. Source check (20 November 2026)

1. **Prefactor.** The phase-space Jacobian is displayed as `π/m`; with `μ = m v⊥²/(2B)` one gets
   `d³r d³v = (2π/m) dψ dα dℓ dμ dv∥`. Unresolved (depends on the source's `μ` convention). It
   affects only the positive constant, so the Lean formula keeps a general `C > 0`; no verified
   statement depends on it.
2. **Vanishing condition (corrected).** The source's eq. 2.23 (`ad = bc`) is necessary but not
   sufficient: the integrand vanishes iff `ad = bc` **and** `ac + bd ≥ 0`
   (`aeIntegrand_eq_zero_iff`); antiparallel vectors satisfy `ad = bc` with a positive integrand
   (`aeIntegrand_pos_of_antiparallel`). Physical form: `itgIntegrand_eq_zero_iff`.
3. **Pure density gradient.** The extracted eqs. 2.25–2.26 did not follow from 2.23 as read. The
   claim itself is proved directly: with `η = 0`, `κ_α = −ω*`, `κ_ψ = 0` satisfies the constraints
   and gives `A = 0` in every geometry (`itg_ae_zero_of_no_temperature_gradient`,
   `groundState_constraints_flat`).

## 3. Verified results

`Theory/Kinetic/ITGAvailableEnergy.lean`, namespace `PlasmaLean.Kinetic.ITGAE`: nonnegativity
(Cauchy–Schwarz through the Lagrange identity), the corrected vanishing condition, the
isodynamic reduction `2(−ac)₊` (eq. 2.28), scaling (`A → t⁴A` with the prefactor), the
integrated formula's nonnegativity, and the `η = 0` fixture.

**Physics remark.** Because parallel dynamics is neglected, `ω_ψ` is the *local* radial `∇B`
drift, not its bounce average. Omnigeneity (C2) does not make it vanish; only an isodynamic field
(`B = B(ψ)` on the tube) does. So this AE measures something C2 does not, which is why it belongs
in the turbulence part of the contract and not as a restatement of C2.

## 4. Next steps (Q-35)

- (b) The stability windows `0 ≤ η ≤ 2/3` and `η ≥ η_B` (source eqs. 2.30–2.34), first in the
  isodynamic reduction.
- (c) The Boozer link: in Boozer coordinates `α = θ − ιφ`, `ℓ ∝ φ`:
  `∂_α B|_{ψ,φ} = ∂_θ B` and `∂_ψ B|_{α,φ} = ∂_ψ B + ι′ φ ∂_θ B` (the shear term is secular in
  `φ`). The `BoozerField` structure has `B`, `Bψ`, `Bθ`, `Bφ` and `ι` but not `ι′`; add it as a
  parameter.
- (d) A certified value or bound on the Dommaschk tori (workstation; needs the vacuum Boozer data
  of N-34 on each certified torus).
