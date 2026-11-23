# Physically meaningful theorem endpoints

This is a selective, human-readable map from proved Lean declarations to physical
interpretations and their hypotheses. It complements the
[model assumptions](model-and-assumptions.md), [transport roadmap](roadmaps/transport.md),
and [orbital-relaxation roadmap](roadmaps/orbital-relaxation.md); it is **not** a second
generated theorem catalog or a list of retained-audit exceptions. The linked Lean
statements, rather than the summaries here, are authoritative.

A theorem about an explicitly defined benchmark or response kernel is not
automatically a theorem about a measured observable, a limiting theory, or an
unrestricted material. The distinction is indicated in each section.

## Periodic projector Berry curvature

Source: [Transport/Topology.lean](../LeanCondensedMatter/Transport/Topology.lean).

| Lean theorem | Physical statement and exact scope |
| --- | --- |
| `QuantumTheory.Transport.Topology.PeriodicBlochProjector.berryCurvature_periodic` | The real projector Berry curvature satisfies `Ω(k + G; u, v) = Ω(k; u, v)` for reciprocal-lattice vector `G`. The theorem assumes a *supplied* smooth reciprocal-lattice-periodic orthogonal-projector family on a finite-dimensional complex Hilbert space. |
| `QuantumTheory.Transport.Topology.PeriodicBlochProjector.berryCurvature_eq_pointwiseBerryCurvature_of_rankOne` | The gauge-invariant formula `i Tr(P [∂ᵤP, ∂ᵥP])` equals the pointwise eigenvector Berry curvature when `P = |n⟩⟨n|` and the two projector derivatives have the **supplied local rank-one derivative expressions**. It does not assume a global smooth eigenvector gauge. |

Neither theorem constructs an occupied-band projector from a gapped Bloch
Hamiltonian, evaluates a Brillouin-zone integral, proves Chern-number
integrality, or identifies a quantized Hall conductivity.

## Clean two-band curvature

Sources: [MassiveDirac/Model/Berry/Symmetry.lean](../LeanCondensedMatter/Models/MassiveDirac/Model/Berry/Symmetry.lean),
[MassiveDirac/Model/Berry/Bridge.lean](../LeanCondensedMatter/Models/MassiveDirac/Model/Berry/Bridge.lean),
and [RashbaExchange/Model/Interband.lean](../LeanCondensedMatter/Models/RashbaExchange/Model/Interband.lean).

| Lean theorem | Physical statement and exact scope |
| --- | --- |
| `QuantumTheory.Models.MassiveDirac.berryCurvature_oppositeBand` | Exchanging the upper and lower bands reverses the *closed-form* massive-Dirac Berry curvature at fixed parameters and momentum. |
| `QuantumTheory.Models.MassiveDirac.berryCurvature_neg_mass` | Reversing the time-reversal-breaking mass changes the sign of that curvature at fixed band and momentum: `Ω_b(-m) = -Ω_b(m)`. |
| `QuantumTheory.Models.MassiveDirac.pointwiseBerryCurvature_xy_eq_berryCurvature` | The pointwise eigenbasis curvature in the physical `x-y` directions equals the massive-Dirac closed formula `-s_b m v²/(2 E³)`, **provided `E ≠ 0`** (nondegenerate two-band point). |
| `QuantumTheory.Models.RashbaExchange.forceMatrixBerryCurvature_eq_berryCurvature` | The gauge-independent force-matrix interband curvature equals the Rashba–exchange closed form `-s_b Δ α_R²/(2 |d|³)` when the model's spin-orbit energy is **nonzero**. |

The unconditional algebraic closed-form identities should not be used as
claims about geometric eigenbundles at a band degeneracy. Curvature identities
alone do not prove an integrated anomalous Hall conductivity.

## Finite-response and relaxation-time conductivity

Sources: [Parabolic2DEG/Response.lean](../LeanCondensedMatter/Models/Parabolic2DEG/Response.lean)
and [MassiveDirac/Conductivity/Longitudinal/BornRelaxationTime.lean](../LeanCondensedMatter/Models/MassiveDirac/Conductivity/Longitudinal/BornRelaxationTime.lean).

| Lean theorem | Physical statement and exact scope |
| --- | --- |
| `QuantumTheory.Models.Parabolic2DEG.finiteCutoffConductivityTensor_hallComponent_eq_zero_of_ne` | The off-diagonal Hall projection vanishes for the **isotropic one-band parabolic benchmark** (`i ≠ j`). This is an exact cancellation of the model's finite-cutoff angular response, not a universal no-Hall theorem. |
| `QuantumTheory.Models.Parabolic2DEG.broadeningTransportLifetime_mul_lorentzianNormalization_eq_bastinStredaTracePrefactor` | The finite-parameter convention `τ_η = ℏ/(2η)` and Lorentzian normalization `η/π` give `τ_η (η/π) = ℏ/(2π)`, assuming `params.IsRegular` (in particular `η > 0`). No zero-broadening limit is taken. |
| `QuantumTheory.Models.MassiveDirac.zeroTemperatureRelaxationTimeLongitudinalConductivity_bornTransportLifetime_eq` | For a metallic positive-energy Fermi surface, the microscopic scalar-disorder Born **transport lifetime inserted into the RTA benchmark** gives `σₓₓ = e² ℏ v²(ε_F²-m²) / [π W(ε_F²+3m²)]`. Assumptions include `v ≠ 0`, `ℏ > 0`, `W > 0`, and `|m| < ε_F`. |
| `QuantumTheory.Models.MassiveDirac.disorderStrength_mul_zeroTemperatureRelaxationTimeLongitudinalConductivity_bornTransportLifetime_eq` | Under the same assumptions, `W σₓₓ = e² ℏ v²(ε_F²-m²) / [π(ε_F²+3m²)]`, exhibiting the finite coefficient of the RTA benchmark's `1/W` scaling. |

The Born-RTA formulas use a transport lifetime obtained from the specified
Born scattering model. They do **not** identify this benchmark with the exact
disorder-averaged Kubo–Středa conductivity or prove the physical `W → 0`,
DC, regulator-removal, or thermodynamic limit.

## Discrete orbital angular relaxation

Source: [OrbitalRelaxation/OctahedralScattering.lean](../LeanCondensedMatter/Models/OrbitalRelaxation/OctahedralScattering.lean).

The kernel samples **six Cartesian directions** `±e₁, ±e₂, ±e₃` and
uses nonnegative scattering weights `W(1)`, `W(-1)`, and `W(0)`.
This finite cubic grid is not the continuous, rotationally invariant sphere.

| Lean theorem | Physical statement and exact scope |
| --- | --- |
| `QuantumTheory.Models.OrbitalRelaxation.octahedral_momentumRate` | The degree-one (momentum) collision eigenvalue is `I₁ = 2 W(-1) + 4 W(0)`. |
| `QuantumTheory.Models.OrbitalRelaxation.octahedral_degreeTwoRate` | The nontrivial diagonal degree-two (quadrupole) rate is `I₂ = 6 W(0)`; it depends only on the orthogonal-scattering channel for this grid. |
| `QuantumTheory.Models.OrbitalRelaxation.octahedral_degreeTwoRate_eq_legendre` | That same `I₂` equals the **finite sum** of scattering weights multiplied by `1 - P₂(cos θ)` over the six directions. It is not a continuous solid-angle integral. |
| `QuantumTheory.Models.OrbitalRelaxation.octahedral_polarization_eq_exp` | For an explicitly **supplied quasistationary orbital kinetic closure**, `P(t) = P(0) exp[-Γ_L t]` with the model's `Γ_L = orbitalRate(axis, ℏ, (6 W(0))⁻¹, c₁, c₂, r)`. The closure itself is an assumption, not a consequence of the collision kernel theorem. |

These are independently interpretable physical results; auxiliary algebraic
rewrite rules and private proof steps are intentionally not indexed here.
