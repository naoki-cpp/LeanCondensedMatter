# Transport ownership

Generic transport theory is upstream of concrete models. This note records stable ownership
boundaries; implementation history belongs in Git history, not here.

## Public routes

```text
LeanCondensedMatter.Analysis
        ↓
LeanCondensedMatter.Transport
        ├── Core
        ├── Resolvent
        ├── KuboBastin
        ├── Streda
        └── Disorder

LeanCondensedMatter.Transport.Models
        └── MassiveDirac
```

`LeanCondensedMatter.Transport` does not import the concrete `Transport.Models` track.
Representation-independent analysis such as finite-dimensional trace, generic spectral resolvent
algebra, and Lorentzian analysis stays under `LeanCondensedMatter.Analysis`.

## Generic owners

```text
Transport/
├── Core/          physical volume, continuum measure, normalization, conductivity tensor
├── Resolvent/     spectral sides, Green operators, self-energy algebra
├── Analysis/      transport-specific occupation analysis
├── KuboBastin/    Lehmann-to-resolvent and finite spectral sums
├── Streda/        static response kernels, traces, integration, response matrices
└── Disorder/      exact finite disorder, Born, SCBA, ladder algebra
```

The main semantic boundaries are:

- finite spectral index and finite Hilbert-space dimension are separate assumptions;
- ordinary operator trace is introduced only where an operator-valued kernel is traced;
- Středa response matrices are response-level objects, not physical conductivity tensors;
- physical prefactors, volume or continuum normalization, and limiting procedures remain explicit
  before constructing a `Core.ConductivityTensor`;
- generic Transport must not acquire model-specific assumptions from `Transport.Models`.

`Core.ContinuumMeasure` owns the two-dimensional physical-momentum convention
`d²p/(2πℏ)²`. Model-specific angular or radial reductions remain downstream until a reduced measure
normalization has genuine reuse beyond one concrete derivation.

## Resolvent and response boundary

`Resolvent.Basic` owns `SpectralSide`, the `E ± iη` convention, and physical Green-operator names.
Generic bounded-resolvent facts belong upstream in `Analysis.Operator.Spectral.Resolvent`.
`Resolvent.SelfEnergy` owns the two-sided Dyson relation `IsSelfEnergy G₀ G Σ` and its
inverse-difference characterization when compatible inverses are available.

`KuboBastin` owns the finite/pure-point spectral response bridge. `Streda` owns the static
surface/sea operator and traced response representation. `Core.ConductivityTensor` is independent of
either representation.

## Disorder boundary

```text
Finite ──→ Resolvent ──→ AveragedSelfEnergy
  │            │
  └──→ Moments ├──→ Born
               ├──→ Ladder
               └──→ SCBA
```

`Disorder.Finite` owns the normalized finite ensemble. `Disorder.Resolvent` owns exact clean,
configuration, and averaged Green operators. `Disorder.Moments` owns the exact second-moment action
`C₂(X) = E[Vω X Vω]` and centered-disorder data.

`Disorder.AveragedSelfEnergy` is exact: at nonzero broadening it proves invertibility of the averaged
Green operator on an arbitrary complete complex Hilbert space and defines the canonical
`Σ_exact = G₀⁻¹ - Ḡ⁻¹` satisfying `IsSelfEnergy`.

`Disorder.Born` owns the side-indexed conventional first-Born self-energy, defined by applying the
exact second-moment action to the corresponding clean Green operator.

`Disorder.SCBA` records supplied self-consistent approximation data and derives its side-indexed
consequences. It is not identified with the exact disorder average. `Disorder.Ladder` owns reusable
retarded-advanced ladder algebra for supplied Green operators and does not assume convergence or a
Ward identity.

## Concrete models

`Transport.Models.MassiveDirac` is the public route for the massive-Dirac transport benchmark.
Concrete models may consume generic Transport and Analysis results, but reusable mathematics or
transport infrastructure should be moved upstream rather than duplicated in the model subtree.

## Import boundaries

- generic Transport must not import `LeanCondensedMatter.SecondQuantization`;
- `LeanCondensedMatter.Transport` must not import `LeanCondensedMatter.Transport.Models`;
- model-specific code must not define generic Transport APIs solely for one concrete consumer.
