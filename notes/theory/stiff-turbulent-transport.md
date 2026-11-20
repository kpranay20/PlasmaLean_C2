# Stiff turbulent transport: a model class for microturbulence and the core-temperature cap

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-45` |
| Title | Stiff (critical-gradient) turbulent transport as a mandatory model class; core-temperature cap and no-access theorems; plan for the ITG geometry clause |
| Kind | definition / proof / research approach |
| Addresses | `Q-33` (new); `G-2` (C5), `G-10` (C2), `G-11`; related `Q-13`, `Q-15`, `Q-22`, `Q-28` |
| Depends on | N-20 (available energy, maximum-J), N-40 (kinetic contract, free-energy route); Lean: none for layer 1 (Mathlib only); `Kernel/Transport` for the link in Q-33 (b) |
| Dependency requirement | layer 1 needs no compiled dependency; the kernel link needs the integrated steady balance from `ClassicalRadialSolution` (not proved) |
| Produces | `Theory/Transport/StiffTransport.lean` (layer 1); Q-33; a proposed change to the C5 contract text; the layer-2 source triage (§4) |
| Difficulty | routine (layer 1: integrating-factor comparison); moderate (kernel link); research (layer 2) |
| Status | layer 1: **verified** (compiled, zero warnings, standard axioms; 20 November 2026); layer 2: stated (gyrokinetic contract started in N-46) |
| Lean evidence | `Theory/Transport/StiffTransport`: `core_le`, `core_le_const`, `stiff_limit`, `core_lt_of_cap_lt(_const)`, `stiffFloorAt_criticalGradient`, `logGrad_le_of_floor_zero`, `sharpProfile_stiffSteady` (default build) |
| Audit evidence | not audited |
| Last updated | 20 November 2026: created |

## Purpose and scope

Microturbulence (ITG, TEM, ETG) is present in every hot magnetized plasma with gradients, whatever
the geometry: geometry moves the **critical gradient** at which the turbulent heat flux switches on
and the **stiffness** above it, but does not remove the turbulence. Under the contract, C5 takes
anomalous transport as a supplied scaling, and the transport kernel asks only `D(ψ,T) ≥ 0`
(`Kernel/Transport`, law `D_nonneg`). Nothing forces a C5 claim to account for turbulence; an
optimistic transport law makes burn look easy.

This note makes turbulence a **lower bound on the heat flux** that every admissible turbulence law
must satisfy (the *turbulent floor*), and proves consequences that hold for **every** law in the
class. Since more transport only lowers the core temperature, upper bounds on the core temperature
need only the floor. These are obstruction-type results: they say what turbulence forbids, which is
what C5 must respect.

Why not derive the floor from gyrokinetics (discussion with the user, 20 November 2026): linear
results (thresholds, energetic growth bounds, available energy) follow from a gyrokinetic model;
the saturated flux does not (no saturation theorem, nonlinear gyrokinetic well-posedness partial,
simulated fluxes chaotic and uncertifiable). So the floor stays a named model class (layer 1), its
constants come from geometry (layer 2, provable in a gyrokinetic model contract), and the step from
layer 2 to the constants stays an explicit supplied law (layer 3).

## 1. Model (layer 1)

Steady state, flux-surface averaged, one temperature.

- `ψ ∈ [0,1]`: normalized flux label, axis `0`, edge `1`. `T > 0` with derivative `T'` in the
  interior.
- `g = logGrad T T' = −T'/T`: inverse gradient length in `ψ`.
- `Q(ψ)`: outward heat flow (W) through the surface `ψ`.
- **Turbulent floor** (`StiffFloorAt`): `S(ψ) T(ψ) (g − κ(ψ))₊ ≤ Q(ψ)`, with stiffness `S > 0` and
  critical log-gradient `κ` (supplied by the turbulence model; geometry enters here).
- **Power**: `Q ≤ W` (heating power inside `ψ`; at a steady state `Q = W − radiation`) and
  `W ≤ w̄ S` (heating power per stiffness).

`StiffSteadyProfile T T' Q W S κ w̄` bundles these on the open interval. The floor is a hypothesis
on the realized profile; it is **not** a kernel law (the kernel `D(ψ,T)` cannot depend on `∂ψT`,
so a critical-gradient law is not expressible as a kernel coefficient). For a kernel solution,
`Q = V' D(ψ,T) (−T')` and the floor is a lower bound on `D` along the solution.

**Coordinates.** For `ψ = ρ²`: `g = (a/L_T)/(2ρ)`, so a constant physical threshold `(a/L_T)_crit`
gives `κ(ψ) = (a/L_T)_crit/(2ρ)`, unbounded at the axis, while `∫₀¹ κ dψ = ∫₀¹ (a/L_T)_crit dρ`.
Near the axis both `W` and `S` vanish like `ψ`, so `W ≤ w̄ S` with finite `w̄` is the natural
hypothesis.

## 2. Results (layer 1)

All in `PlasmaLean/Theory/Transport/StiffTransport.lean`, namespace
`PlasmaLean.Transport.Stiff` (compiled, standard axioms only).

| Declaration | Statement |
| --- | --- |
| `neg_deriv_le` | pointwise gradient clamping: `−T' ≤ κ̄ T + w̄` for `κ ≤ κ̄` |
| `core_le` | `T(0) ≤ (T(1) + w̄) · exp(K(1) − K(0))`, `K' = κ̂ ≥ κ`, `κ̂ ≥ 0`, `w̄ ≥ 0` |
| `core_le_const` | `T(0) ≤ T(1) e^{κ̄} + (w̄/κ̄)(e^{κ̄} − 1)`, `κ ≤ κ̄`, `κ̄ > 0` (sharp) |
| `stiff_limit` | `w̄ = 0`: `T(0) ≤ T(1) e^{κ̄}` |
| `core_lt_of_cap_lt`, `core_lt_of_cap_lt_const` | no access: cap `< T_burn` ⇒ `T(0) < T_burn`, for every law in the class |
| `stiffFloorAt_criticalGradient` | witness: the critical-gradient-model flux `S₀ T g (g − κ)₊` satisfies the floor with `S = S₀ κ` |
| `logGrad_le_of_floor_zero` | zero transport is excluded above threshold |
| `sharpProfile`, `sharpProfile_stiffSteady`, `sharpProfile_zero`, `sharpProfile_one` | the cap of `core_le_const` is attained |

**Proof.** Clamping: divide the floor by `S > 0` and expand `T (−T'/T − κ)`. Cap: the function
`T e^{K} + w̄ e^{K(1)} ψ` has derivative `(T' + κ̂T) e^{K} + w̄ e^{K(1)} ≥ −w̄ e^{K} + w̄ e^{K(1)} ≥ 0`
(clamping, and `K` nondecreasing because `κ̂ ≥ 0`); compare its values at `0` and `1`. Sharp
constant form: `(T + w̄/κ̄) e^{κ̄ψ}` is nondecreasing.

**Reading for C5.** In the stiff limit the core can exceed the edge only by the factor
`exp ∫(a/L_T)_crit dρ`. Example: `∫(a/L_T)_crit dρ = 3` gives `T_core ≤ 20 T_edge`, so a 10 keV core
needs `T_edge ≥ 0.5 keV` unless the heating power is large against the stiffness (`w̄`). This is a
geometry-and-edge requirement no choice of turbulence law within the class can evade, and it is
where layer 2 pays off: raising the certified critical gradient raises the cap exponentially.

## 3. Sanity triad

1. Witness: the standard critical-gradient model (Garbet–Imbeaux form, flux `∝ χ_s (g − κ)₊ T g`)
   is in the class (`stiffFloorAt_criticalGradient`), and the class contains a profile attaining
   the cap (`sharpProfile_stiffSteady`).
2. Non-vacuity: a transport law with `Q = 0` cannot sustain a gradient above threshold
   (`logGrad_le_of_floor_zero`); the class excludes "no turbulence".
3. Failure case (to add as a regression theorem): a profile with `T(0)` above the cap and `Q = 0`
   violates the floor; it fits the kernel with `D = 0` away from a regular axis, which is exactly
   the optimistic case the class removes.

## 4. Layer 2: ITG geometry quantities (source triage, 20 November 2026)

Read so far (agent extraction, spot-checked algebra; not yet a source-assessment note):

- **Available energy of the curvature-driven ITG** (Mackenbach et al., J. Plasma Phys., "On the
  curvature-driven ion-temperature-gradient instability and its available energy"): an explicit
  field-line integral (their eq. 2.21) of drift quantities built from `∂_ψ ln B|_{α,ℓ}` and
  `∂_α ln B|_{ψ,ℓ}`; `A ≥ 0` (Lagrange identity); vanishing condition eq. 2.23; with
  `B ≈ B₀` in the energy, stability windows `0 ≤ η ≤ 2/3` and `η ≥ η_B`. Geometry-dependent, so
  it discriminates candidates. Issues found: (i) phase-space Jacobian `π/m` vs `2π/m` (factor 2 in
  the prefactor); (ii) vanishing needs `ac + bd ≥ 0` besides `ad = bc`; (iii) the pure-density-
  gradient formulas 2.25–2.26 did not follow from 2.23 as read. Check against the source before
  formalizing.
- **Energetic growth bound, adiabatic electrons** (Helander–Plunk, Part 1; Podavini et al.,
  Part 5): `γ ≤ (|η_i ω*_i|/2) √(G/((1+τ)(1+τ−G₀)))` with Bessel-function moments `G₀, G₁, G₂`;
  geometry enters only through `b_i = k_⊥²ρ_i²` (Part 5 eq. 2.16; the displayed `k_α|∇α|²` is
  probably `k_α²`). Rigorous given the linear model, but weakly geometry-dependent: a ceiling, not a
  discriminator.
- **Critical-gradient model** (Roberg-Clark, Plunk, Xanthopoulos, arXiv:2208.05727): the natural
  supplier of `κ`; text not yet extracted; appears partly heuristic.

Layer-2 targets in order: (a) the AE algebra (positivity, vanishing condition, η windows) as
lemmas about the integrand (lean-ready once the source checks pass); (b) a linear local
electrostatic gyrokinetic **model contract** (flux tube, adiabatic electrons) with the free-energy
balance and the bound `γ ≤ D/H`; this is a new model commitment and needs a user decision;
(c) certified evaluation of an ITG geometry quantity on a candidate (Dommaschk tori).

## 5. Proposed contract change (needs user decision)

C5 currently reads "anomalous transport is a stated, supplied scaling". Proposed: "anomalous
transport is a supplied law **satisfying the turbulent floor** `StiffFloorAt` with stated `κ`, `S`
(critical gradient and stiffness), and C5 conclusions that are upper bounds on temperature hold
for every law in that class". Existing C5 results (Solov'ev band, Stellaris windows) are not
affected until restated.

## Outputs and next dependencies

- Q-33 (a): done (compiled 20 November 2026).
- Q-33 (b): derive `Q ≤ W` from a steady `ClassicalRadialSolution` (integrate the divergence form).
- Q-33 (c): user decision on §5.
- Q-33 (d): layer 2 (§4), starting with the source checks.
