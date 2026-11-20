# Linear local electrostatic gyrokinetics: model contract, free energy and growth bounds

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-46` |
| Title | Linear gyrokinetic model contract (operator form), free-energy balance and the Helander–Plunk growth bound |
| Kind | definition / formalization |
| Addresses | `Q-34` (new); `Q-33` (d), `G-10`, `G-2` |
| Depends on | N-45 (turbulence programme), N-40 (free-energy route), N-20; sources: Helander & Plunk, J. Plasma Phys. 88 (2022) 905880207 (Part 1); Podavini et al., Part 5 (eqs. 2.1–2.17) |
| Dependency requirement | none compiled; the abstract layer uses Mathlib only |
| Produces | `Theory/Kinetic/LinearGyrokinetic.lean`; Q-34 (b)–(d) |
| Difficulty | routine (abstract layer); moderate (discretized instance); research (continuum instance, certified geometry inputs) |
| Status | abstract layer **verified** (20 November 2026: zero warnings, standard axioms); instances open |
| Lean evidence | `LinearGKModel`, `eigen_balance`, `H_ge`, `growth_le`, `growth_le_of_qn`, `eigen_re_eq_zero_of_no_drive`, `growth_bound_indep_A`, `energy_balance` (default build) |
| Audit evidence | not audited |
| Last updated | 20 November 2026: created (model commitment approved by the user) |

## Purpose and scope

The turbulence programme (N-45) needs geometry-dependent ITG quantities that are theorems of a
stated kinetic model. This note fixes that model: one Fourier mode of the linear, collisionless,
electrostatic gyrokinetic equation in a flux tube, kinetic ions, adiabatic electrons,

`∂ₜ g + v∥ ∂_l g + i ω_d g = (e F₀/T) J₀ (∂ₜ φ + i ω*^T φ)`, `λ φ = e ∫ J₀ g d³v`.

Out of scope: kinetic electrons, electromagnetic terms, collisions (they only decrease the free
energy), nonlinear saturation.

## Operator form (the contract)

| Symbol | Meaning |
| --- | --- |
| `V` | nonadiabatic ion distributions, `⟪g, h⟫ = ⟨∫ T conj(g) h / F₀ d³v⟩` |
| `U` | potentials along the field line, `⟪φ, ψ⟫ = ⟨conj(φ) ψ⟩` |
| `A` | `v∥ ∂_l + i ω_d`: streaming and magnetic drift, **the geometry** |
| `J`, `K` | `J φ = e J₀ F₀ φ/T`, `K g = e ∫ J₀ g d³v`, adjoint (`adj`) |
| `Ω` | `ω*^T e J₀ F₀ φ/T`, the gradient drive |
| `λ` | `n e²/T_i + n e²/T_e` |

The equation is `ġ + A g = J φ̇ + i Ω φ` with `φ = λ⁻¹ K g`. **Supplied clause `skew`:**
`re ⟪g, A g⟫ = 0`. For the physical operator this is integration by parts along `l` and the
reality of `ω_d`; it must be **proved** for each concrete instance (Q-34 (b), (c)).

## Results (verified)

- `energy_balance`: `d/dt H(g(t)) = 2 D(g(t))`, `H = ‖g‖² − λ‖φ‖²`, `D = re ⟪g, iΩφ⟫`.
- `eigen_balance`: an eigenmode `g e^{st}` has `(re s) H = D`.
- `H_ge`: `H ≥ (1 − c)‖g‖²` when `‖K g‖² ≤ c λ ‖g‖²`; physically `c = Γ₀(b)/(1+τ) < 1`.
- `growth_le`, `growth_le_of_qn`: `D ≤ Λ H` on `V` ⇒ every eigenmode has `re s ≤ Λ`.
- `eigen_re_eq_zero_of_no_drive`: no gradients, no growth.
- `growth_bound_indep_A`: `H` and `D` do not involve `A`.

**Consequence.** The energetic bound cannot distinguish geometries except through `K` (that is,
`k⊥ρ`). This is the formal version of the observation in Part 5, and the reason the
geometry-sensitive ITG work must go through the available energy or the critical gradient.

## Limits (as of 20 November 2026)

The theorems hold for any operators satisfying the contract. No concrete instance exists yet, so
nothing here ranks or certifies a candidate. `skew` is assumed, not proved, for the physical
operators.

## Outputs and next dependencies

- Q-34 (b): a discretized instance (finite velocity grid, periodic or decaying field-line grid,
  central differences) with `skew` and `adj` proved; this makes the contract non-vacuous and gives
  a computable `Λ` (a generalized eigenvalue problem).
- Q-34 (c): the continuum instance (weighted `L²`, `|J₀| ≤ 1`, ballooning domain).
- Q-34 (d): certified `ω_d(l)`, `k⊥(l)`, `B(l)` along a field line of a certified torus.
