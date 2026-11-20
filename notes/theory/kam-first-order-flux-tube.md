# First-order flux-tube data from certified KAM tori

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-48` |
| Title | First-order neighbourhood data (shear `ι′`, normal displacement) from certified KAM tori, for the ITG available energy on a candidate and a first-order Boozer surrogate for C2 |
| Kind | method / research approach (method note for N-34 §5 and N-47 §5) |
| Addresses | `Q-36` (new); `Q-35` (d), `G-10`, `Q-16` |
| Depends on | N-33/N-34 (certified Dommaschk tori C and A, per-torus vacuum Boozer angles `VacuumBoozerTorus`), `notes/theory/kam-route.md` (hypotheses H3 transversal frame `N₀`, H4 torsion `T`), N-47 (`ITGBoozer`, `ITGDriftChart`) |
| Dependency requirement | certified `K`, `N`, `⟨T⟩` enclosures on a torus (the KAM certificate already bounds `|⟨T⟩⁻¹|`; two-sided enclosures and the frame are new outputs) |
| Produces | Q-36 statements; a plan; claims to check (§3) |
| Difficulty | research: the identification of `⟨T⟩` with `dι/dψ` in the flow (ELP-S) setting, the derivative of the Boozer angle map, and certification cost |
| Status | stated (proposal, 20 November 2026); nothing verified |
| Lean evidence | none (uses `ITGBoozer`, `ITGDriftChart` downstream) |
| Audit evidence | not audited |
| Last updated | 20 November 2026: created |

## Purpose and scope

The ITG available energy on the Dommaschk candidate (Q-35 (d)) and C2 for the actual field are
blocked by the same gap: no Boozer chart off the certified tori (audit AC-1, N-34 §5.2, N-47 §5).
But the source of the available energy works in a **linearized flux tube**: it needs, along a field
line on one surface, `|B|`, its in-surface derivatives, the shear `ι′`, and the derivative of `|B|`
across the surface at fixed field-line label, i.e. **first-order** neighbourhood data, not a chart
on an open set. This note proposes to take that data from the KAM certificate, which already
works with a transversal frame and a twist (torsion) condition.

## 1. What is needed, per certified torus

From `ITGBoozer`/`ITGDriftChart`: at points of the torus, in Boozer angles,
`∂_θ B` (in-surface; available per torus via `VacuumBoozerTorus`), `ι` (certified), and

- `ι′ = dι/dψ` (shear), and
- `∂_ψ B|_{θ_B, φ_B}`: the derivative of `|B|` along `e_ψ = ∂x/∂ψ` at fixed Boozer angles.

`|∇ψ|` along the line scales `a, b, c, d` together (N-47 §5) and also follows from `e_ψ`.

## 2. The proposed source: the parametrization-method frame

In the a-posteriori KAM framework (kam-route.md, FHL / Haro et al.; ELP-S for divergence-free
fields), an invariant torus `K` comes with the frame `[DK, N]`, `N = DK·A + N₀B`, in which the
linearized dynamics is triangular with torsion `T(θ)`. The standard consequences, **to be checked
in the flow setting used here**:

1. The torus family is Whitney-smooth in the frequency on the Diophantine set, with
   `∂_ω K = DK·a + N·⟨T⟩⁻¹` (the normal part of the displacement is `⟨T⟩⁻¹` per unit frequency).
2. With the symplectic form normalized to the flux 2-form `i_B vol` (field-line flow), the action
   conjugate to the angle is the toroidal flux `ψ`, so `⟨T⟩ = dω/dψ`, i.e. `ι′` up to the `2π`
   conventions.
3. Hence `e_ψ = ∂K/∂ψ = ∂_ω K · ι′ = N + DK·(ι′ a)` at fixed KAM angles; at fixed **Boozer**
   angles it gains the derivative of the angle change `λ` across the family, which solves the
   linearized cohomological equation (first-order data again).

## 3. Claims to check (none established)

- (C1) The ELP-S flow-version twist equals `dι/dψ` with the flux normalization (cf. kam-route.md
  §2: the ELP-S twist is "an explicit average over the approximate torus").
- (C2) The Whitney derivative `∂_ω K` exists on the certified Diophantine torus and is enclosed by
  the same `ℓ¹_ν` machinery as `K` (one more cohomological solve).
- (C3) The derivative of the Boozer angle map across the family solves a linear cohomological
  equation on the torus.
- (C4) Cost: about one more cohomological solve per torus plus enclosures; to be estimated against
  the C1 chain (≈ 12 min wall, ≤ 5.4 GB, N-34 §5.3).

## 4. Uses

- **ITG (Q-35 (d)):** certified `ω_α`, `ω_ψ` along field lines on tori C and A, hence the
  integrand `boozerIntegrand` and (with the ground-state solve) an available-energy value or bound
  per torus.
- **C2 (Q-16, N-34 §5.3):** a first-order Boozer surrogate between R1 (agreement on the surfaces
  only) and R2 (an approximate volume chart): the surrogate agrees with the field to first order at
  each certified torus. Still a model, to be labelled as such.

## 5. Next steps

Check (C1) against ELP-S Definition 6.1 and the FHL/Haro bookkeeping (source study); then a
numerical prototype on torus C (untrusted oracle): `⟨T⟩` vs a finite-difference `ι′` between tori C
and A, and `∂_ψ|B|` from `∂_ω K`. Only then a certification plan.
