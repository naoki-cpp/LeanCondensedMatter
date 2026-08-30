# Transport ownership

The transport stack is organized by mathematical ownership rather than by the first concrete
consumer. Generic transport theory remains upstream of fermionic realizations and concrete model
benchmarks.

```text
QuantumTheory.LinearResponse
          ↓
QuantumTheory.Transport
      ↙            ↘
fermionic adapters   concrete neutral models
                     e.g. AnomalousHall/MassiveDirac
```

General analysis infrastructure sits further upstream. In particular, the bundled ordinary
finite-dimensional operator trace is owned by `Analysis/Operator/FiniteTrace.lean`, generic bounded
resolvent spectrum exclusion, shifted inverse algebra, and eigenvector action are owned by
`Analysis/Operator/Spectral/Resolvent.lean`, while the model-independent Lorentzian approximate-
identity kernel, weighted-window analysis, and regular-factor pole extraction are owned by
`Analysis/Lorentzian/{Kernel,Weighted,Pole}.lean`. Transport consumes these primitives rather than
owning them.

## Physical source hierarchy

Canonical generic owners now live in physical subdirectories rather than in a flat
`Transport/` namespace:

```text
Transport/
├── Core/
│   ├── FiniteVolume.lean
│   ├── ConductivityNormalization.lean
│   └── FiniteConductivityTable.lean
├── Resolvent/
│   ├── Basic.lean
│   ├── SelfEnergy.lean
│   ├── Spectral.lean
│   └── EnergyDerivative.lean
├── Analysis/
│   ├── BandOccupation.lean
│   └── ZeroTemperatureOccupation.lean
├── KuboBastin/
│   ├── PurePoint.lean
│   ├── Finite.lean
│   ├── OccupationInterpolation.lean
│   ├── Occupation.lean
│   └── CommonEnergy.lean
├── Streda/
│   ├── OperatorKernel.lean
│   ├── TraceKernel.lean
│   ├── Integration.lean
│   ├── GeneralizedStatic.lean
│   ├── TraceSpectral.lean
│   ├── TraceRepresentation.lean
│   └── SpectralEnergyIntegral.lean
└── Disorder/
    ├── Finite.lean
    ├── Resolvent.lean
    ├── Moments.lean
    ├── BornCommon.lean
    ├── RetardedBorn.lean
    ├── AdvancedBorn.lean
    └── SCBA.lean
```

The stable public grouping modules are `Transport.Core`, `Transport.Resolvent`,
`Transport.KuboBastin`, `Transport.Streda`, and `Transport.Disorder`. The project-level
`LeanCondensedMatter.Transport` imports those five groups. General finite-dimensional trace,
generic bounded-resolvent spectral algebra, and Lorentzian kernel/weighted-window/pole infrastructure
are exported instead by `LeanCondensedMatter.Analysis`. The retired `Transport.Foundations`,
`Transport.ResolventAPI`, historical flat generic Transport leaf modules, and the declaration-free
`Transport.KuboBastin.FiniteTrace` compatibility shim were removed after repository-wide consumer
audits showed no remaining imports.

All historical flat Transport and massive-Dirac AHE compatibility modules have now been removed
after repository-wide consumer audits showed no remaining imports. `scripts/check_transport_hierarchy.py`
continues to enforce the canonical public umbrellas and core hierarchy constraints without carrying
compatibility-forwarder machinery.

## Semantic Kubo–Bastin / Středa boundary

The pure-point and finite spectral-index restrictions are separate ownership boundaries:

```text
KuboBastin/PurePoint
        ↓  [Fintype ι]
KuboBastin/Finite
```

`KuboBastin/PurePoint.lean` owns the complete-Hilbert-space Lehmann-to-retarded-resolvent algebra for
one pure-point transition and does not assume a finite spectral index. `KuboBastin/Finite.lean`
introduces `Fintype ι` only when those transitions are assembled into ordinary finite sums and
packaged as finite `ResponseChannel` responses. Its named `finiteKuboBastinSpectralVertexSum`
separates the two-vertex contribution from the explicit observable-variation expectation used by
the complete response. It does not manufacture an ordinary operator-trace representation from an
already-computed scalar response.

Ordinary finite-dimensional operator trace is a representation-independent analysis primitive owned
by `Analysis/Operator/FiniteTrace.lean`. Mathlib already supplies `LinearMap.trace`, trace cyclicity,
and the derivative-composition machinery needed by this file; the project-level addition is only the
continuous-linear functional bundling and its thin reusable consequences. The first genuine traced
Bastin kernels are obtained in the static Středa layer, where `Streda/TraceKernel.lean` applies that
analysis primitive to the canonical operator kernels from `Streda/OperatorKernel.lean`. Thus finite
spectral index and finite Hilbert-space dimension remain explicit, distinct assumptions, while
ordinary traces are introduced only where an operator-valued kernel actually exists to trace.

`KuboBastin/Occupation.lean` and `KuboBastin/CommonEnergy.lean` remain on the Kubo–Bastin side of
the boundary: their transition-level APIs are pure-point, while complete response/kernel sums use
the finite spectral-index layer. They do not define a Středa surface or sea term. Genuine Středa
ownership begins at `Streda/OperatorKernel.lean`, where the Smrčka–Středa surface primitive and
residual sea kernel are introduced.

`Analysis/Operator/Spectral/Resolvent.lean` owns the representation-independent bounded-resolvent
facts: nonreal exclusion from a self-adjoint spectrum, two-sided shifted-resolvent inverse identities,
and resolvent action on an eigenvector under explicit spectral exclusion. `Resolvent/Basic.lean`
keeps the retarded/advanced `SpectralSide`, the `E ± iη` parameter convention, Green-operator names,
and physical specializations of those generic facts. `Resolvent/Spectral.lean` owns the side-indexed
and pure-point specializations, including squared pure-point action. Pure-point Kubo–Bastin and
Středa spectral expansions consume these results rather than re-owning resolvent algebra.

`Resolvent/SelfEnergy.lean` owns the model-independent two-sided Dyson relation
`IsSelfEnergy G₀ G Σ`, stated without requiring inverses as both
`G = G₀ + G₀ Σ G` and `G = G₀ + G Σ G₀`. Keeping both noncommutative orientations makes the
abstraction stable under adjunction. The module proves the inverse-difference characterization
`Σ = G₀⁻¹ - G⁻¹` when compatible two-sided inverses are supplied. Approximation layers may construct
candidate self-energies without thereby proving this exact relation for a separately truncated Green
approximation.

## Disorder boundary

The exact/approximate split remains explicit:

```text
Disorder/Finite
   ├──→ Disorder/Resolvent ───────→ BornCommon ──┬──→ RetardedBorn
   └──→ Disorder/Moments ─────────→ BornCommon   └──→ AdvancedBorn
                       └────────────────────────────→ SCBA

Transport/Resolvent.Basic ──→ Disorder/Resolvent
                         └──→ SCBA
Transport/Resolvent.SelfEnergy ───────────────────→ SCBA
```

`Disorder/Finite` owns the exact finite ensemble and normalized scalar/operator averages.
`Disorder/Resolvent` owns the exact side-indexed clean/configuration Green operators together with
conventional retarded/advanced specializations. Its exact Dyson identities remain explicitly
retarded/advanced because adjunction reverses noncommutative product order. `Disorder/Moments` owns
the canonical bounded complex-linear exact second-moment action `C₂(X) = E[Vω X Vω]`, proves its
finite-average and adjoint-compatibility properties, and owns the separate `IsCentered` property
used to cancel first-order disorder insertions.

`Disorder/BornCommon` owns the canonical side-indexed first-Born data shared by both physical
specializations: `bornSelfEnergy`, `bornResolventApproximation`, the orientation-aware
`exactSecondOrderRemainder`, `bornClosureError`, and `BornClosureHypothesis`, together with centered
first-order cancellation and the common algebra `G₀ + G₀ Σ G₀`. The exact remainder keeps the
side-dependent multiplication order inherited from the configuration Dyson identities, while its
retarded/advanced values, the self-energy, the truncated Green, and the closure error are proved to
be related by adjunction. Conventional retarded/advanced names remain in `Disorder/RetardedBorn`
and `Disorder/AdvancedBorn` as physical specializations. The centered exact-average decomposition
proofs remain in those sibling modules because they consume orientation-specific configuration
Dyson identities; the siblings must not import one another.

The Born self-energy and approximation objects use the canonical exact second moment and therefore
do not themselves require centered disorder. Centering is required only when an exact averaged
Dyson identity is reduced by cancelling the first-order contribution. In particular, the truncated
Born resolvent expression is not asserted to satisfy the exact `IsSelfEnergy` relation. SCBA uses
the same canonical `exactSecondMomentCLM` directly in its supplied fixed-point equations; there is no
second covariance function or separately supplied linearity/adjoint-compatibility assumption. The
SCBA Green and self-energy solution itself remains approximation data and is not identified with the
exact disorder average, while its supplied two-sided inverse equations do imply the abstract
`IsSelfEnergy` relation on either spectral side.

## AHE benchmark hierarchy

The massive-Dirac benchmark is physically structured as

```text
Transport/AnomalousHall/MassiveDirac/
├── Model/
│   ├── Basic.lean
│   ├── Operator.lean
│   ├── CurrentBridge.lean
│   ├── Occupation.lean
│   ├── Spectral.lean
│   └── OperatorSpectral.lean
├── Intrinsic/
│   ├── BerryBridge.lean
│   ├── BerrySymmetry.lean
│   ├── Response.lean
│   └── Conductivity.lean
├── Streda/
│   ├── Response.lean
│   └── Integral.lean
└── Bastin/
    ├── Berry / Bands / Limit / Lorentzian / Occupation / ...
    ├── Pole*       -- model-specific pole factor/window/specialization bridge
    ├── Radial*     -- finite-cutoff radial domination/DCT chain
    └── CleanConductivity.lean
```

`MassiveDirac.Model`, `.Intrinsic`, `.Streda`, and `.Bastin` are the public benchmark layers.
The historical flat Model, Intrinsic, Středa, and Bastin forwarding modules were removed after
repository-wide consumer audits showed no remaining imports. Concrete implementations now live only
under the canonical `MassiveDirac/{Model,Intrinsic,Streda,Bastin}/` hierarchy.

Within the concrete benchmark, `Model/Operator.lean` owns the exact matrix-to-bounded-operator
realization (`DiracHilbert`, Hamiltonian/current operators, self-adjointness, the bounded free-system
adapter, and the matrix/operator trace bridge). `Model/CurrentBridge.lean` owns both the matrix and
bounded canonical charge-current identifications. `Model/OperatorSpectral.lean` owns the transported
band-projector algebra and gauge-free projector resolvent. These are response-independent model
facts and are consumed directly by `Propagator`, disorder, and Bastin code without importing the
model-specific Středa layer.

`MassiveDirac/Streda/Response.lean` now owns only the pointwise Bastin/Středa trace specialization,
and `Streda/Integral.lean` owns the finite-energy surface/sea decomposition. The retired
`Streda/CurrentOperatorBridge.lean` and `Streda/Spectral.lean` paths must not be recreated as
compatibility shims; repository consumers use the canonical `Model` owners directly.

This hierarchy is not permission for AHE to own reusable analysis. Generic band-state occupation and
Fermi-surface notions plus zero-temperature occupation/Fermi-edge weights remain under
`Transport/Analysis/`, where their transport/occupation semantics live. The scalar Lorentzian
kernel/tail analysis, local-constant weighted-window extraction, and regular-factor pole extraction
are representation-independent and live upstream under `Analysis/Lorentzian/`; both generic
Transport and the massive-Dirac specialization consume those analysis primitives.

## Generic / concrete boundary

Files under generic Transport must not import `LeanCondensedMatter.SecondQuantization`. Fermionic
finite-Fock, lattice, directional-current, Fermi-state, and Peierls-contact realizations remain in
`SecondQuantization/Fermionic/Transport` and specialize the neutral owners.

`LeanCondensedMatter.Transport` must not import the concrete AHE umbrella. The project root imports
`LeanCondensedMatter.Transport` and `LeanCondensedMatter.Transport.AnomalousHall` as separate public
tracks.

Physical formula, sign, normalization, limiting-order, and approximation semantics must not change
as part of path/ownership migration.
