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
| Status | C1 supported by source study (with corrected attribution and normalization) and **confirmed numerically** on tori A, B, C (untrusted); C2, C3 supported by source study (derived, conditional); nothing in Lean |
| Lean evidence | `Theory/Kinetic/ITGShear` (use of a shear lower bound: `boozer_bad_curvature`, `itg_stability_condition_fails`; two-point lemma: `exists_tail_near`, `boozer_two_points`, `boozer_bad_curvature_of_shear` in `Theory/Kinetic/ITGTwoPoint`) |
| Audit evidence | not audited |
| Last updated | 20 November 2026: created; source study and numerical check of C1 added (§6, §7) |

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

## 6. Source study (20 November 2026; agent report, sources read verbatim on arXiv)

Sources: ELP-S arXiv:2104.08149v3 §6; Figueras–Haro–Luque arXiv:1601.00084 §2;
de la Llave–González–Jorba–Villanueva, Nonlinearity 18 (2005); Haro–Luque arXiv:1711.05515.

- **Attribution correction.** The frame quantities `N₀`, `B = −(DKᵀΩN₀)⁻¹`, `Ω` and the torsion
  `T = N(θ+ω)ᵀΩ DF N` quoted in kam-route.md H3/H4 (and in §2 above) are from **FHL Theorem 2.5**,
  a theorem for exact symplectic **maps** (for a 3-D field: through a Poincaré map). **ELP-S
  Theorem 6.2** (flows) uses the frame `(DK, n/|n|²)`, `n = ∂_1K × ∂_2K` (eqs. 6.4, 6.7), and the
  twist constant `T = [A]·ω^⊥`, `A = −G_K⁻¹ DKᵀ (DB + DBᵀ) n/|n|²` (Def. 6.1, eq. 6.3). It fixes
  the direction of the frequency (so `ι`), and says nothing about families.
- **C1** (supported with modifications): the twist is proportional to the shear, not equal to it.
  Map route: `⟨T⟩ = dι/dψ_t` (flux form, action `ψ_t`; `2π dι/dψ_t` with action `ψ_t/2π`).
  Flow route (ELP-S): `n/|n|²` is a **volume** coordinate, and the twist is the rate of change of
  the frequency direction per unit enclosed volume.
- **C2** (supported, derived, conditional): `∂_ωK = DK·a + N⟨T⟩⁻¹` (maps); for flows the normal
  part of `∂_sK` is constant. Needs a Whitney-C¹ family over the Diophantine set (a separate
  theorem: dLGJV §1, refs Van02, dlLV00), an invertible twist, and a gauge for `⟨a⟩`.
- **C3** (supported by standard structure): the change to Boozer angles solves a magnetic
  differential equation on the torus; its derivative across the family solves another one, whose
  right side needs `∂_sK` and `ω′` from C2 (two strip losses).

## 7. Numerical check of C1 (untrusted; `scripts/dommaschk_kam/twist_vs_shear.py`)

In the conventions of `scripts/dommaschk_kam/twist.py` (angles in turns, `θ/2π`, `φ/π` over one
field period, `ω = ι/2`, field-line time normalized by `cc = 1/⟨1/B^φ⟩`, `ω_s = cc(ω/π, 1/π)`),
the prediction is

  **`T = (cc²/2π²) · dι/dV`**, `V` = volume enclosed per field period,

because `n/|n|²` sweeps unit volume per unit parameter area and only the `ω^⊥` component of the
frequency change survives the cross product. Tori A, B, C at `N × M = 32 × 26` (double precision;
invariance errors 4e-11, 9e-10, 7e-12), `dι/dV` by centred differences from neighbouring Galerkin
tori at `ι ± δ`:

| torus | `T` | prediction | ratio, `δ = 2e-4` | ratio, `δ = 1e-4` |
| --- | --- | --- | --- | --- |
| A | 5.3708e-2 | 5.3708e-2 | 1.000035 | 1.0000086 |
| B | 3.9514e-2 | 3.9511e-2 | 1.000261 | 1.000065 |
| C | 5.5787e-2 | 5.5787e-2 | 1.000025 | 1.0000062 |

The deviation falls by about 4 when `δ` halves (second-order differences), so the ratio converges
to 1. The raw ratio `T/(dι/dΦ)` is not constant (0.0240, 0.0226, 0.0246), because
`dΦ/dV` (0.363, 0.356, 0.366) varies: the shear in flux is
`dι/dΦ = (2π²/cc²) · T · dV/dΦ`.

**Consequence.** On a certified torus, the certified twist (with `cc` and `dΦ/dV`) gives `ι′`
without computing neighbouring tori; with C2 the normal displacement per unit flux is
`(n/|n|²)·dV/dΦ` (normal part). Remaining for Q-35 (d): certified enclosures of `T`, `cc`, `dΦ/dV`
(the first two are torus integrals the certificate pipeline can enclose; `dΦ/dV` is
`⟨B·∇φ⟩`-type, to be derived), the Whitney-C¹ theorem for C2, and the Boozer-angle derivative (C3).

## 8. The project's own KAM twist is `2π ι′` (20 November 2026; untrusted numerics)

The certified KAM chain (`Design/KamFlowStepG`, `FlowFieldG`) uses the frame `V₀ = K − A`
(radial from the axis approximation) with area density `w = D/R^p`, `p = 7`, i.e.
`w = R B^φ`, the flux density of the section; torsion `T₀ = (Y × V₀)/(w W₀²)`, `W₀ = ∂_θK × V₀`
(`scripts/dommaschk_kam/kam_constants.py`, `torsion`). Its average, against `dι/dΦ` from
neighbouring Galerkin tori (`δ = 1e-4`, §7):

| torus | `⟨T₀⟩` | `dι/dΦ` | ratio | ratio/2π − 1 |
| --- | --- | --- | --- | --- |
| A | 14.06296222 | 2.238171 | 6.2832383 | +8.4e-6 |
| B | 10.96866183 | 1.745606 | 6.2835844 | +6.4e-5 |
| C | 14.26392119 | 2.270160 | 6.2832240 | +6.2e-6 |

The residuals equal the finite-difference errors of §7, so **`⟨T₀⟩ = 2π dι/dΦ`** in the project
frame, with no further factor (the `2π`: `Φ` is the full toroidal flux, the action conjugate to
the angle in turns is `Φ/2π`).

**Consequence: a certified lower bound on the shear already exists.** The torus-C chain certifies
the twist constant `tauC = 14.1623 ≤ |⟨Talg⟩|` (`Design/DommaschkKamCAdmOut`, `consts_sharp`; on-demand,
workstation-checked) and propagates the margin `τ′ = τ − kTc·eM > 0` to the KAM torus
(`DommaschkKamCConsts.dk_τ'`). With the identity above this reads
`|dι/dΦ| ≥ 14.16/2π ≈ 2.254` at torus C (true value ≈ 2.270). What is missing:

1. **an upper bound** (two-sided enclosure): `torsion_bounds` (`DommaschkKamCAdmFrame`) gives
   `|⟨YZ⟩| ≥ m_Y − n_Y ζ` from a centre; the same argument gives `|⟨YZ⟩| ≤ M_Y + n_Y ζ` once the
   centre average is enclosed above. This needs a re-run of the admissibility chain (heavy:
   workstation; the laptop used on 20 November 2026 has 6 GB of RAM);
2. **the identification** `⟨Tor⟩ = 2π ι′` as a theorem: it needs the Whitney-C¹ family (claim C2),
   not in Lean; until then the certified number is the twist, and its reading as shear is supported
   by the numerics above;
3. `cc` and `dΦ/dV` are not needed in this frame (they were for the ELP-S normalization of §7).

## 9. Using the shear lower bound: sheared tubes contain bad curvature (verified)

`Theory/Kinetic/ITGShear.lean`. In Boozer units (`ψ` = toroidal flux / 2π) the certified twist
of §8 reads directly `|ι′| = |dι/dψ| ≥ 14.16` at torus C (modulo the identification). The
shear term `ι′φ∂_θB` of `∂_ψB|_{α,φ}` grows along the field line, so:

- `exists_bad_curvature`, `boozer_bad_curvature`: if `|ι′| ≥ s₀ > 0`, `|∂_ψB| ≤ M`, `0 < B ≤ B_max`,
  and `∂_θB` reaches `≥ c` and `≤ −c` at two points beyond the tube length
  `L = (M + K B_max)/(s₀ c)`, then one of them has `∂_ψ ln B|_{α,φ} < −K`, whatever the sign of
  `ι′` (bad curvature for a peaked density);
- `itg_stability_condition_fails`: with `K = |∂_ψ ln T|`, the source's stability condition (2.35)
  fails there: it can hold only on a flux tube shorter than `L`, and a larger certified shear makes
  `L` shorter.

Supplied, not certified: the two points (equidistribution of the irrational line and mean-zero
`∂_θB`), and `M`, `c`, `B_max` along the line (they need the chart data, Q-35 (d)).
Correction recorded: an earlier suggestion that the C2 bridge needs `ι′ ≠ 0` was wrong; its
"twist" `ι_min` is `ι` itself.

## 10. The two points exist (verified, 21 November 2026)

`Theory/Kinetic/ITGTwoPoint.lean` removes the supplied two-point hypothesis of §9:

- `exists_tail_near`: tail density of an irrational rotation (`n ≥ N`), from the density of
  `ℤa + ℤp` in Mathlib plus a walk with a small positive-multiple step;
- `exists_deriv_neg_of_periodic`: `∂_θB` of a `θ`-periodic `B` takes both signs unless it vanishes
  on the whole section (monotone + periodic ⇒ constant);
- `boozer_two_points`: on a surface with `B` periodic in `θ` and `φ`, `ιP/p` irrational and
  `∂_θB ≢ 0` on one section, every field line has points with `∂_θB ≥ c` and `≤ −c` beyond every
  length;
- `boozer_bad_curvature_of_shear`: with `|ι′| ≥ s₀ > 0` and global bounds `|∂_ψB| ≤ M`,
  `0 < B ≤ B_max` on the surface, **every field line has points with `∂_ψ ln B|_{α,φ} < −K` for
  every `K`**.

Remaining inputs for torus C: `M`, `B_max`, a section with `∂_θB ≠ 0` (chart data, Q-35 (d)); the
shear bound via the twist identification (§8); `ι` irrational is certified (Diophantine).

## 11. The conditional part of the family theorem (verified, 21 November 2026)

`Theory/KAM/FamilyDerivative.lean`: in an abstract torus algebra (average, `𝓛` with
`avg ∘ 𝓛 = 0` and `ker 𝓛 = constants`), the linearized frame equations of a differentiable family,
`𝓛ξ₂ = 0`, `𝓛ξ₁ + Tξ₂ = ω′`, imply `ξ₂` constant, **`ω′ = ⟨T⟩ξ₂`** (`frequency_derivative`: twist =
frequency change per unit normal displacement), `ξ₂ = ω′/⟨T⟩` when `⟨T⟩ ≠ 0`
(`normal_displacement`, claim C2), `ξ₁` unique up to a constant; fixtures `trivialFrame`
(accepted) and `no_family_of_zero_twist` (rejected). With the flux-normalized frame (§8) this is
twist = shear.

The remaining gap is now exactly two statements:
(G1) the tori near a certified one form a Whitney-C¹ family over the Diophantine set whose
derivative satisfies the linearized frame equations (a theorem from the literature; source study
in progress);
(G2) an instance of `FrameData` on the strip algebra `FA` (`ker 𝓛 = constants` for a Diophantine
frequency; likely short from `Theory/KAM/Cohomological.cohSol_unique`).

