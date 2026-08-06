# Transport roadmap

This track separates four boundaries that must not be conflated:

1. Hilbert-space dimension;
2. physical finite volume versus a thermodynamic limit;
3. ordinary finite trace, trace-class trace, and trace per unit volume;
4. a conductivity derived from causal response versus a formula adopted as a definition.

## Reusable bounded data

`QuantumTheory.Transport.BoundedSystem H` is defined on an arbitrary complete complex Hilbert
space. It stores:

- a bounded self-adjoint Hamiltonian;
- bounded self-adjoint current observables;
- signed carrier charge and a positive reduced Planck constant;
- zero-temperature Fermi energy;
- positive retarded/advanced broadening;
- a self-adjoint idempotent Fermi projector commuting with the Hamiltonian.

It does not assume `FiniteDimensional ℂ H`. The Fermi projector is supplied as data; construction
of the discontinuous spectral projector by functional calculus is a separate theorem.

`QuantumTheory.Transport.FiniteVolumeSystem H` adds only a positive physical volume. An
infinite-dimensional Hilbert space may still describe a finite-volume model. Infinite-volume
conductivity requires a trace per unit volume or a controlled thermodynamic limit and is not
obtained by deleting the volume field.

The retarded and advanced parameters are fixed as

```text
zᴿ(E, η) = E + iη,
zᴬ(E, η) = E - iη.
```

The bridge `BoundedSystem.toBoundedFreeSystem` forgets transport-specific data and exposes the
Hamiltonian and `ℏ` to the general bounded linear-response API. The reverse direction is
intentionally unavailable because a free-dynamics system does not determine current or Fermi data.

## Derived response chain

The implemented logical chain is

```text
time-dependent perturbation
  → causal Kubo response
  → continuity-derived Peierls current and contact response
  → finite-time harmonic response
  → stationary positive-lag representation
  → fixed-positive-rate observation-time limit
  → finite pure-point Lehmann sum plus contact term
  → finite-volume electric-field conductivity normalization.
```

The fermionic conductivity layer can reuse the volume of `FiniteVolumeSystem` through
`FiniteVolumeConductivityConvention.ofTransportSystem`. This copies only volume data; matching a
model Hamiltonian and current with the abstract transport observables remains an explicit theorem
obligation.

## Next resolvent layer

Issue #366 should define

```text
Gᴿ(E, η) = (zᴿ(E, η) I - H)⁻¹,
Gᴬ(E, η) = (zᴬ(E, η) I - H)⁻¹
```

and prove invertibility for `η > 0`, the adjoint relation, the resolvent identity, and the energy
derivative identity at the strongest dimension-independent bounded-operator level supported by
Mathlib.

Issue #367 should then add finite-dimensionality only where ordinary traces and finite spectral
sums require it. Its Kubo–Bastin expression must be proved equal to the already-derived finite
conductivity, including the same current, charge, `ℏ`, volume, frequency, broadening, degeneracy,
and contact conventions.

## Explicit deferrals

The current bounded clean slice does not claim:

- unbounded Hamiltonian, current, position, or polarization operators;
- equivalence of electromagnetic gauges;
- finite-temperature Fermi–Dirac response;
- disorder averaging, Born approximations, or vertex corrections;
- a general non-self-adjoint trace-class ideal;
- trace per unit volume or a thermodynamic limit;
- a DC or zero-broadening limit without an explicit convergence theorem.
