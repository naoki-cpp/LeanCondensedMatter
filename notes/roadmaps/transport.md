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
  → exact configuration and averaged Green operators
  → exact second moment C₂(X) = E[Vω X Vω]
  → averaged-Green invertibility at nonzero broadening
  → exact self-energy Σ_exact = G₀⁻¹ - Ḡ⁻¹
```

The exact averaged Green operator is invertible at nonzero broadening on an arbitrary complete
complex Hilbert space. The resulting `exactSelfEnergy` satisfies the two-sided `IsSelfEnergy`
relation and is not identified with Born or SCBA data.

The first-Born layer is kept directly in `Disorder.Born`: `bornSelfEnergy side` is the exact
second-moment action evaluated on the clean Green operator for that spectral side. Retarded and
advanced uses specialize the side only at their consumers; no separate R/A Born routing modules or
closure/truncation API are maintained.

## SCBA and ladder boundary

SCBA stores supplied self-consistent approximation data using the same exact second-moment action
`C₂`; it does not assert existence of the nonlinear fixed point or equality with the exact disorder
average.

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
