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

LeanCondensedMatter.Transport.Analysis   (opt-in analytical utilities)

LeanCondensedMatter.Transport.Models
        └── MassiveDirac
```

`LeanCondensedMatter.Transport` does not import the concrete `Transport.Models` track or the opt-in
`Transport.Analysis` package. Representation-independent analysis such as finite-dimensional trace,
generic spectral resolvent algebra, and Lorentzian analysis stays under `LeanCondensedMatter.Analysis`.

## Generic owners

```text
Transport/
├── Core/          physical volume, normalization, conductivity tensor
├── FiniteConductivityTable.lean
│                  finite Lehmann + contact + positive-volume E-field normalization
├── Resolvent/     signed spectral regulator, physical spectral sides, self-energy algebra
├── Spectral/      response-neutral adapters from supplied spectral data to resolvent algebra
├── Analysis/      occupations, 2D continuum measure, angular harmonics, polar Fourier, relaxation time
├── KuboBastin/    Lehmann-to-resolvent response algebra and finite spectral sums
├── Streda/        static response kernels, traces, integration, response matrices
└── Disorder/      exact finite disorder, Green operators, Born, SCBA, ladder algebra
```

The main semantic boundaries are:

- finite spectral index and finite Hilbert-space dimension are separate assumptions;
- ordinary operator trace is introduced only where an operator-valued kernel is traced;
- Středa response matrices are response-level objects, not physical conductivity tensors;
- physical prefactors, volume or continuum normalization, and limiting procedures remain explicit
  before constructing a `Core.ConductivityTensor`;
- `FiniteConductivityTable` is an electrical-conductivity adapter downstream of the generic
  `QuantumTheory.LinearResponse.FiniteLehmannTable`; the generic Lehmann evaluator does not depend
  on contact terms, physical volume, driving frequency normalization, or electric-field conversion;
- generic Transport must not acquire model-specific assumptions from `Transport.Models`.

`Analysis.BandOccupation` owns only arbitrary occupation-law composition with band energies.
`Analysis.ZeroTemperatureOccupation` owns the strict scalar Fermi step and its pointwise properties;
`Analysis.ZeroTemperatureBandFilling` owns zero-temperature occupied regions, Fermi surfaces, and
filled/empty/partially-filled band predicates; and `Analysis.ZeroTemperatureLorentzian` owns the
finite-window Fermi-edge integrals, arctangent formulas, broadening limits, and isolated-pole
weights. This split lets arbitrary-occupation and band-filling consumers avoid the heavier
Lorentzian edge analysis.

`Analysis.ContinuumMeasure` owns the opt-in two-dimensional physical-momentum convention
`d²p/(2πℏ)²`; it is not a dimension-independent transport invariant. `Analysis.AngularHarmonics`
owns the reusable constant/first/second harmonic
coefficient decomposition and ordinary full-angle cancellation laws. `Analysis.PolarFourier`
consumes the same coefficient data for phase-weighted radial-axis reduction while keeping the
zeroth, first-cosine, and second-cosine kernels explicit. Model layers supply coefficient values;
Pauli algebra, propagator data, and radial physics remain model-owned.

## Resolvent and response boundary

`Resolvent.Basic` owns the signed spectral parameter `z(E, γ) = E + iγ`, `SpectralSide`, and the
physical `E ± iη` specializations. Analytic resolvent theorems are stated at arbitrary `γ` whenever
the argument does not intrinsically depend on retarded/advanced branch semantics. The conversion
from a physical side and broadening to the analytic regulator is owned by
`SpectralSide.regulator`; physical consumers should use `side.regulator η` instead of reconstructing
its `side.sign * η` representation. `spectralParameter` and `spectralResolvent` are the canonical
side-indexed physical owners, while conventional retarded/advanced names are retained as consumed
specializations.

Generic bounded-resolvent facts belong upstream in `Analysis.Operator.Spectral.Resolvent`.
`Resolvent.Spectral` specializes those facts to the arbitrary signed-regulator transport parameter
without importing response data. `Spectral.PurePoint` is the neutral adapter that combines this
generic resolvent action with `PurePointLehmannData`; Kubo–Bastin and Středa both consume that
adapter rather than owning duplicate pure-point spectral proofs.

`Resolvent.SelfEnergy` owns the representation-independent two-sided Dyson relation
`IsSelfEnergy G₀ G Σ` and its inverse-difference characterization when compatible inverses are
available.

`KuboBastin` owns the finite/pure-point response algebra built on that spectral adapter. `Streda` owns the static
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
wrapper. `Disorder.Ladder` owns the RA kernel for supplied Green operators and the generic
fixed-point/resummation algebra for bounded complex-linear endomorphisms. Conditional resummation
and uniqueness use the canonical `IsUnit (1 - L)` hypothesis on the space where the ladder is
represented; no geometric-series convergence is assumed. Concrete invariant subspaces, such as the
massive-Dirac in-plane Pauli coefficient space, may therefore use the same resummation theorem after
proving their restricted shift is a unit. The disorder layer does not expose separate inverse-data,
one-rung, or residual routing APIs and does not assume a Ward identity.

## Concrete models

`Transport.Models.MassiveDirac` is the public route for the massive-Dirac transport benchmark.
Its explicit clean Pauli Green operator and continuum Born self-energy follow the same split as the
generic disorder layer: arbitrary-regulator definitions/theorems own the analytic calculation, while
side-indexed objects are retained only at reusable physical boundaries such as broadening limits,
Born-Dyson dressing, and RA vertex calculations. Physical-side specializations consume the canonical
`SpectralSide.regulator` conversion rather than depending on the sign representation directly.

The massive-Dirac continuum normalization keeps each physical factor at the narrowest model-local
stage that owns it. `Disorder.Born.SelfEnergy` owns the full-angle radial measure used by the Born
self-energy; `Disorder.ContinuumMeasurePrefactor` owns one external scalar-disorder line times one
bare physical-momentum measure independently of where angular reduction is performed; and
`Conductivity.Normalization` separately owns the Bastin/Středa trace prefactor and the combined
trace-plus-measure normalization. `MassiveDirac.ContinuumMeasureProvenance` records the bridge
equalities between these stages, including the placement of the angular `2π`. Momentum-space
non-crossing responses consume the combined conductivity normalization only after their response
integral is formed. Real-space crossed Fourier blocks already contain their physical momentum
measures upstream, so a later crossed conductivity boundary must consume only the remaining
trace/current normalization rather than attach another momentum measure.

Concrete models may consume generic Transport and Analysis results, but reusable mathematics or
transport infrastructure should be moved upstream rather than duplicated in the model subtree.

## Import boundaries

- generic Transport must not import `LeanCondensedMatter.SecondQuantization`;
- `LeanCondensedMatter.Transport` must not import `LeanCondensedMatter.Transport.Models`;
- model-specific code must not define generic Transport APIs solely for one concrete consumer.
