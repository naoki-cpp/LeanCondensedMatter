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

## Implemented clean response chain

The proved logical chain is

```text
time-dependent perturbation
  → causal Kubo response
  → continuity-derived Peierls current and contact response
  → finite-time harmonic response
  → stationary positive-lag representation
  → fixed-positive-rate observation-time limit
  → finite pure-point Lehmann sum plus contact term
  → finite-volume electric-field conductivity normalization
  → finite Kubo–Greenwood and Kubo–Bastin forms
  → static finite-rate target with contact and normalization retained
  → regularized Středa surface-plus-sea decomposition.
```

The dimension-independent resolvent layer proves retarded/advanced invertibility, adjoint,
difference, and energy-derivative identities for bounded self-adjoint Hamiltonians. Finite
dimensionality is added only where ordinary traces and finite pure-point sums require it.

The static bridge does not identify the causal conductivity with an occupation-weighted Bastin
integral by definition. The Peierls contact cancellation, switching-rate/energy-broadening
conversion, volume normalization, and scalar prefactors remain visible in a finite Ward hypothesis.

Finite two-level and two-site dimer models validate zero-current cases, simultaneous current-sign
reversal, nonzero traced values, self-adjoint hopping/current constructions, and pointwise
Bastin–Středa agreement.

## Implemented exact disorder and first Born boundary

The exact finite-disorder layer now provides:

```text
finite normalized ensemble Ω
  → self-adjoint impurity potentials Vω
  → exact configuration Hamiltonians Hω = H₀ + Vω
  → configuration-wise finite static conductivities
  → normalized finite conductivity average
  → configuration-wise Ward/Bastin representation
  → averaged traced and spectral Bastin representations.
```

No probability law beyond an explicit normalized finite weight is assumed. The ensemble average
remains outside each exact configuration response, and contact plus finite-volume normalization
remain inside it.

The weak-scattering Born boundary then separates exact and approximate statements:

- exact operator-valued finite averages;
- explicit centering and covariance data;
- exact first and once-iterated retarded Dyson identities;
- exact vanishing of the averaged first-order term under centering;
- an exact second-order remainder retaining the full configuration resolvent;
- a clean-propagator Born self-energy;
- a named Born resolvent approximation;
- an exact closure error;
- equality with the approximation only under an explicit closure hypothesis.

This layer does not include SCBA, a dressed internal propagator, or a vertex correction.

## Selected conserving vertex continuation

Issue #372 selects the next vertical slice, documented in
`notes/roadmaps/impurity-vertex-correction.md` and implemented by #688:

```text
finite-dimensional SCBA retarded/advanced fixed points
  + one complex-linear adjoint-compatible covariance superoperator
  → retarded–advanced ladder kernel from the same covariance
  → corrected bounded vertex under explicit invertibility
  → finite charge-vertex Ward-consistency theorem.
```

The SCBA solution is not defined to be the exact disorder average. The ladder retains non-crossing
impurity contractions and excludes crossed diagrams. The first conservation result is weaker than
a full electromagnetic Ward–Takahashi identity and does not yet identify a vertex-corrected dressed
bubble with the exact Kubo–Středa conductivity.

## Explicit deferrals

The current program does not claim:

- unbounded Hamiltonian, current, position, or polarization operators;
- equivalence of electromagnetic gauges;
- a general finite-temperature Fermi–Dirac response theorem;
- uncontrolled equality between exact disorder averages and Born or SCBA solutions;
- crossed impurity diagrams, weak localization, or localization transitions;
- skew-scattering or side-jump decompositions;
- a complete electromagnetic Ward–Takahashi identity;
- a vertex-corrected Kubo–Bastin or Středa conductivity theorem before its source/contact bridge is proved;
- a general non-self-adjoint trace-class ideal;
- trace per unit volume or a thermodynamic limit;
- a DC or zero-broadening limit without an explicit convergence theorem.
