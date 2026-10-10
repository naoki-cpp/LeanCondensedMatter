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

LeanCondensedMatter.Models
        ├── MassiveDirac
        ├── Parabolic2DEG
        └── RashbaExchange
```

`LeanCondensedMatter.Transport` does not import concrete `Models` or the opt-in
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
`d²p/(2πℏ)²` and its exact full-angle radial prefactor `2π/(2πℏ)²`; these are continuum conventions,
not dimension-independent transport invariants. `Analysis.AngularHarmonics`
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
surface/sea operator and traced response representation, together with the representation-level
`ℏ/(2π)` trace prefactor and its composition with an explicitly supplied continuum-measure
normalization. `Core.ConductivityTensor` is independent of either representation.

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

## Scalar-impurity T-matrix ownership

MassiveDirac.Disorder.TMatrix.ScalarImpurity owns the scalar-impurity parameters, unit-guarded
T-matrix and self-energy algebra, operator-norm bounds, and the quadratic small-strength remainder
for an explicitly supplied 2×2 Green loop. It depends on the model's matrix/operator realization,
without importing continuum measures or real-space propagators.

TMatrix.BornDysonLoop owns the finite-cutoff Born-Dyson loop at the spatial origin, its zero-disorder
clean-loop identity, and the Born self-energy coefficient under W = n_imp v_imp². The physical
momentum measure is attached by the loop realization exactly once; the mean-potential term remains
separate. TMatrix is the package entry point for these two responsibilities.
## Concrete models

The `Models.RashbaExchange` family owns its Rashba-exchange Hamiltonian, finite spectral data,
clean bounded-operator realizations in `Operator`, retarded/advanced resolvents in `Green`,
Berry/force-matrix bridges, and finite Bastin/Středa response. Generic trace, measure, and conductivity constructions remain upstream
under `Transport`.

`Models.Parabolic2DEG` is the public route for the finite isotropic parabolic-band
normalization benchmark. It keeps effective mass, chemical potential, radial cutoff, positive
spectral broadening, signed charge/current convention, reduced Planck constant, and momentum-measure
normalization explicit. Its clean Hamiltonian and current vertices are in `Model`, while
`Green` owns the finite-broadening scalar/operator resolvents. The pointwise response consumes the
common finite-broadening Středa surface kernel `RA - (RR + AA)/2` through these operators. The reduced
finite-cutoff response remains a response-level object until the named `ℏ/(2π)` Kubo trace
prefactor is attached; only then is it exposed through `Core.ConductivityTensor`. No thermodynamic,
cutoff-removal, or zero-broadening limit is part of this benchmark.

`Models.MassiveDirac` is the public route for the massive-Dirac transport benchmark.
Its explicit clean Pauli Green operator and continuum Born self-energy follow the same split as the
generic disorder layer: arbitrary-regulator definitions/theorems own the analytic calculation, while
side-indexed objects are retained only at reusable physical boundaries such as broadening limits,
Born-Dyson dressing, and RA vertex calculations. Physical-side specializations consume the canonical
`SpectralSide.regulator` conversion rather than depending on the sign representation directly.

The fixed-cutoff metallic Born-Dyson zero-broadening boundaries share one explicit
`FixedCutoffMetallicBornRegime` domain package. It owns only the common velocity, mass, probe-energy,
disorder, reduced-Planck, cutoff, metallic-shell, and cutoff-orientation data. Conductivity charge
normalization, real Born-renormalization bounds, and ladder determinant nonvanishing remain explicit
at the result boundaries that consume them; the regime package is not a replacement for the scaling
domain or for generic denominator APIs.

The massive-Dirac continuum normalization keeps each physical factor at the narrowest owner.
`Analysis.ContinuumMeasure` owns both the bare physical-momentum measure and its exact full-angle
radial prefactor. `Disorder.ContinuumMeasurePrefactor` owns one external scalar-disorder line times
one bare physical-momentum measure independently of where angular reduction is performed, while
`Streda.ConductivityNormalization` owns the model-independent Bastin/Středa trace prefactor and its
composition with continuum normalization. `MassiveDirac.ContinuumMeasureProvenance` retains only
model-specific bridge equalities involving the disorder stage. Momentum-space non-crossing
responses consume the physical-momentum conductivity normalization only after their response
integral is formed. Real-space crossed Fourier blocks already contain their physical momentum
measures upstream, so a later crossed conductivity boundary must consume only the remaining
trace/current normalization rather than attach another momentum measure.

Concrete models may consume generic Transport and Analysis results, but reusable mathematics or
transport infrastructure should be moved upstream rather than duplicated in a concrete model.
The canonical top-level owner of all three concrete benchmark families is `Models`;
`Transport` contains only reusable model-independent theory.

## Import boundaries

- generic Transport must not import `LeanCondensedMatter.SecondQuantization`;
- generic `Transport` modules must not import concrete `Models` modules;
- model-specific code must not define generic Transport APIs solely for one concrete consumer.
