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
├── Resolvent/     signed spectral regulator, physical spectral sides, self-energy algebra
├── Analysis/      transport-specific occupation analysis
├── KuboBastin/    Lehmann-to-resolvent and finite spectral sums
├── Streda/        static response kernels, traces, integration, response matrices
└── Disorder/      exact finite disorder, Green operators, Born, SCBA, ladder algebra
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

`Resolvent.Basic` owns the signed spectral parameter `z(E, γ) = E + iγ`, `SpectralSide`, and the
physical `E ± iη` specializations. Analytic resolvent theorems are stated at arbitrary `γ` whenever
the argument does not intrinsically depend on retarded/advanced branch semantics. Physical
consumers specialize with `γ = side.sign * η` or directly with `±η`.

Generic bounded-resolvent facts belong upstream in `Analysis.Operator.Spectral.Resolvent`.
`Resolvent.SelfEnergy` owns the representation-independent two-sided Dyson relation
`IsSelfEnergy G₀ G Σ` and its inverse-difference characterization when compatible inverses are
available.

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
configuration, and averaged Green operators at arbitrary signed regulator `γ`. Exact configuration
Dyson expansions are owned at arbitrary nonzero `γ`; physical consumers specialize the regulator
locally when branch semantics are required.

`Disorder.Moments` owns the exact second-moment action `C₂(X) = E[Vω X Vω]` and centered-disorder
data.

`Disorder.AveragedSelfEnergy` is exact: at arbitrary nonzero `γ` it proves invertibility of the exact
averaged Green operator on an arbitrary complete complex Hilbert space and defines
`exactSelfEnergyOfRegulator = G₀⁻¹ - Ḡ⁻¹`, satisfying `IsSelfEnergy`.

`Disorder.Born` owns `bornSelfEnergyOfRegulator`, the conventional first-Born self-energy obtained by
applying the exact second-moment action to the clean Green operator at arbitrary `γ`.

`Disorder.SCBA` records supplied self-consistent approximation data and derives its side-indexed
consequences. Here retarded/advanced branch semantics are part of the physical approximation data,
so SCBA remains explicitly `SpectralSide`-aware rather than being treated as an analytic regulator
wrapper. `Disorder.Ladder` owns the RA kernel for supplied Green operators, finite fixed-point
iteration, and conditional resummation/uniqueness under the canonical `IsUnit (1 - L_RA)`
hypothesis. It does not expose separate inverse-data, one-rung, or residual routing APIs and does not
assume convergence or a Ward identity.

## Concrete models

`Transport.Models.MassiveDirac` is the public route for the massive-Dirac transport benchmark.
Its explicit clean Pauli Green operator and continuum Born self-energy follow the same split as the
generic disorder layer: arbitrary-regulator definitions/theorems own the analytic calculation, while
side-indexed objects are retained only at reusable physical boundaries such as broadening limits,
Born-Dyson dressing, and RA vertex calculations.

Concrete models may consume generic Transport and Analysis results, but reusable mathematics or
transport infrastructure should be moved upstream rather than duplicated in the model subtree.

## Import boundaries

- generic Transport must not import `LeanCondensedMatter.SecondQuantization`;
- `LeanCondensedMatter.Transport` must not import `LeanCondensedMatter.Transport.Models`;
- model-specific code must not define generic Transport APIs solely for one concrete consumer.
