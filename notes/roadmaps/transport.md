# Transport roadmap

This track separates four boundaries that must not be conflated:

1. Hilbert-space dimension;
2. physical finite volume versus a thermodynamic limit;
3. ordinary finite trace, trace-class trace, and trace per unit volume;
4. a conductivity derived from causal response versus a formula adopted as a definition.

## Reusable bounded boundaries

The current Transport architecture deliberately does **not** package all transport assumptions into
a monolithic `BoundedSystem` or `FiniteVolumeSystem`. Reusable data are composed at the narrowest
layer that needs them.

The bounded dynamics input is `QuantumTheory.LinearResponse.BoundedFreeSystem H`, defined on an
arbitrary complete complex Hilbert space. It stores only:

- a bounded self-adjoint Hamiltonian;
- a positive reduced Planck constant.

Transport adds physical volume independently through `QuantumTheory.Transport.PositiveVolume`.
The volume is not inferred from Hilbert-space dimension: an infinite-dimensional Hilbert space may
still describe a finite-volume model, while an infinite-volume conductivity requires a trace per
unit volume or a controlled thermodynamic limit.

Finite pure-point spectral data, response-channel data, current/contact information, occupations,
and ordinary finite-dimensional traces remain separate inputs owned by the layers that use them.
This avoids making a single transport wrapper carry assumptions that are irrelevant to many
resolvent or response theorems.

The retarded and advanced parameters remain

```text
zᴿ(E, η) = E + iη,
zᴬ(E, η) = E - iη.
```

Their shared implementation is organized through the side-indexed `SpectralSide` API in
`Transport.Resolvent.Basic` and `Transport.Resolvent.Spectral`, with retarded and advanced names
retained as the public physical specializations.

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
spectral-action, squared spectral-action, and energy-derivative identities for bounded
self-adjoint Hamiltonians. Finiteness is introduced only at the layer that actually needs it: a
finite spectral-index sum requires a `Fintype` index, while the ordinary operator trace requires
finite-dimensional Hilbert space.

`Transport.Core` owns representation-independent bookkeeping such as positive physical volume,
electric-field normalization, finite scalar conductivity tables, and the ordinary finite-dimensional
trace. `Transport.KuboBastin` owns the pure-point Lehmann-to-resolvent bridge and finite/common-energy
spectral representations. The finite layer names the two-vertex sum independently from the explicit
observable-variation expectation so the static Středa boundary can consume only the part that has an
energy representation. Genuine ordinary traced Bastin kernels belong to the static
`Transport.Streda` layer rather than to a finite-frequency Kubo–Bastin compatibility wrapper.

The static bridge does not identify the causal conductivity with an occupation-weighted Bastin
integral by definition. Contact terms, switching-rate/energy-broadening conversion, volume
normalization, scalar prefactors, and the hypotheses needed to identify a concrete response with an
energy representation remain explicit at their corresponding bridge.

Finite model realizations, including the massive-Dirac anomalous-Hall benchmark, are downstream of
the generic Transport layers and should not be used to define generic spectral-analysis APIs unless
a genuinely reusable proof pattern has first been demonstrated.

## Implemented exact disorder and first Born boundary

The exact finite-disorder layer provides:

```text
finite normalized ensemble Ω
  → self-adjoint impurity potentials Vω
  → exact configuration Hamiltonians Hω = H₀ + Vω
  → exact side-indexed clean/configuration Green operators
  → retarded/advanced Green specializations and configuration-wise Dyson identities
  → exact finite scalar/operator ensemble averages
  → canonical bounded complex-linear second moment C₂(X) = E[Vω X Vω].
```

The canonical second-moment map is exact finite-ensemble data. Its complex linearity and adjoint
compatibility are proved from the finite sum and self-adjoint impurity potentials rather than
supplied as extra covariance assumptions. No probability law beyond an explicit normalized finite
weight is assumed. The ensemble average remains outside each exact configuration response.

The first-Born boundary then separates exact and approximate statements:

- the explicit centered-disorder property `E[Vω] = 0`;
- side-indexed `bornSelfEnergy` and `secondOrderBornGreen` plus shared averaging/closure algebra in `Disorder.BornCommon`;
- exact first and once-iterated side-indexed Dyson identities in both left and right orientations;
- exact vanishing of the averaged first-order term under centering;
- side-indexed exact second-order remainders retaining the full configuration resolvent;
- conventional retarded and advanced Born self-energy and second-order Green-truncation names as physical specializations;
- named exact closure errors and side-indexed closure hypotheses;
- equality with the second-order Born Green truncation only under an explicit closure hypothesis.

The retarded and advanced physical specializations remain siblings. Shared side-indexed Born data,
the orientation-aware `exactSecondOrderRemainder`, `BornClosureHypothesis`, the centered exact-average
decomposition, and R/A-neutral algebra belong in `BornCommon`; conventional physical R/A names stay
in the respective specialization modules. The sibling modules do not import one another.

`secondOrderBornGreen` is specifically the explicit Dyson-series truncation
`G₀ + G₀ Σᴮ G₀`. It is not a Dyson-resummed Green operator and is not asserted to satisfy the exact
`IsSelfEnergy` relation. The first-Born layer does not identify this truncation with the exact
disorder average without the stated closure hypothesis, and it does not introduce a dressed
internal propagator or a vertex correction.

## Selected conserving vertex continuation

Issue #372 selects the next vertical slice, documented in
`notes/roadmaps/impurity-vertex-correction.md` and implemented by #688:

```text
canonical bounded complex-linear second moment C₂
  + finite-dimensional SCBA retarded/advanced fixed points using C₂
  → retarded–advanced ladder kernel generated by the same C₂
  → corrected bounded vertex under explicit invertibility
  → finite charge-vertex Ward-consistency theorem.
```

The SCBA solution is not defined to be the exact disorder average. The canonical second-moment map
is exact, while the self-consistent fixed-point solution remains approximation data. The ladder
retains non-crossing impurity contractions and excludes crossed diagrams. The first conservation
result is weaker than a full electromagnetic Ward–Takahashi identity and does not yet identify a
vertex-corrected dressed bubble with the exact Kubo–Středa conductivity.

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
