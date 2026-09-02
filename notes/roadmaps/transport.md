# Transport roadmap

Current ownership is summarized in [`../architecture/transport.md`](../architecture/transport.md).
This file tracks proved chains and open transport targets.

## Proved clean-response chain

```text
time-dependent perturbation
  → causal Kubo response
  → current/contact response
  → finite-time harmonic response
  → finite pure-point Lehmann form
  → finite-volume conductivity normalization
  → Kubo–Greenwood / Kubo–Bastin representation
  → regularized Středa surface-plus-sea response
```

The bounded resolvent layer is dimension-independent. Finite spectral sums require a finite index;
ordinary operator traces require finite-dimensional Hilbert space. These assumptions are kept
separate.

Středa response matrices are not physical conductivity tensors. Physical prefactors, volume or
continuum normalization, and required limits remain explicit before constructing
`Transport.Core.ConductivityTensor`.

## Proved disorder chain

```text
finite normalized ensemble
  → exact configuration and averaged Green operators G(E,γ)
  → exact second moment C₂(X) = E[Vω X Vω]
  → averaged-Green invertibility for γ ≠ 0
  → exact self-energy Σ_exact(E,γ) = G₀(E,γ)⁻¹ - Ḡ(E,γ)⁻¹
```

The exact Green and self-energy analytic core is parameterized by the signed regulator
`z(E,γ) = E + iγ`. Physical retarded/advanced consumers specialize with
`γ = side.sign * η` rather than relying on parallel analytic implementations.

The exact averaged Green operator is invertible for arbitrary nonzero `γ` on an arbitrary complete
complex Hilbert space. `exactSelfEnergyOfRegulator` satisfies the two-sided `IsSelfEnergy` relation
and is not identified with Born or SCBA data.

The first-Born layer is kept directly in `Disorder.Born`:
`bornSelfEnergyOfRegulator E γ = C₂(G₀(E,γ))`. No separate R/A Born routing modules or
closure/truncation API are maintained.

The explicit massive-Dirac clean Green operator, its angular/radial reduction, common continuum Born
denominator, polar-integral bridge, and finite-cutoff continuum Born self-energy use the same
arbitrary-`γ` analytic ownership. Side-indexed forms remain only where broadening-limit, Born-Dyson,
or RA vertex consumers require physical branch semantics.

## SCBA and ladder boundary

SCBA stores supplied self-consistent approximation data using the same exact second-moment action
`C₂`; it does not assert existence of the nonlinear fixed point or equality with the exact disorder
average. Because the supplied fixed-point data distinguish physical retarded and advanced branches,
SCBA remains explicitly `SpectralSide`-aware.

`Disorder.Ladder` owns the reusable retarded-advanced action

```text
L_RA(Γ) = C₂(Gᴿ Γ Gᴬ)
```

and exact finite algebra built from it. Resummation requires an explicit inverse of `I - L_RA`;
convergence and Ward identities are separate targets.

## Open targets

- bridge response-level Středa data to a physical conductivity tensor with explicit normalization;
- vertex-corrected Kubo–Bastin/Středa conductivity with stated source/contact assumptions;
- trace per unit volume and controlled thermodynamic limits;
- justified DC and zero-broadening limits;
- convergence-aware SCBA/ladder results where needed;
- crossed-diagram, weak-localization, skew-scattering, and side-jump extensions;
- unbounded Hamiltonian/current/position operators and gauge-equivalence results.
