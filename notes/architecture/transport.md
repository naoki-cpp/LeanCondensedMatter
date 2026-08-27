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

## Physical source hierarchy

Canonical generic owners now live in physical subdirectories rather than in a flat
`Transport/` namespace:

```text
Transport/
├── Core/
│   ├── FiniteVolume.lean
│   ├── ConductivityNormalization.lean
│   ├── FiniteConductivityTable.lean
│   └── FiniteTrace.lean
├── Resolvent/
│   ├── Basic.lean
│   ├── Spectral.lean
│   └── EnergyDerivative.lean
├── Analysis/
│   ├── BandOccupation.lean
│   ├── LorentzianKernel.lean
│   ├── LorentzianPole.lean
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
`LeanCondensedMatter.Transport` imports those five groups. The retired `Transport.Foundations`,
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

Ordinary finite-dimensional operator trace is a representation-independent primitive owned by
`Core/FiniteTrace.lean`. The first genuine traced Bastin kernels are obtained in the static Středa
layer, where `Streda/TraceKernel.lean` applies that trace to the canonical operator kernels from
`Streda/OperatorKernel.lean`. Thus finite spectral index and finite Hilbert-space dimension remain
explicit, distinct assumptions, while ordinary traces are introduced only where an operator-valued
kernel actually exists to trace.

`KuboBastin/Occupation.lean` and `KuboBastin/CommonEnergy.lean` remain on the Kubo–Bastin side of
the boundary: their transition-level APIs are pure-point, while complete response/kernel sums use
the finite spectral-index layer. They do not define a Středa surface or sea term. Genuine Středa
ownership begins at `Streda/OperatorKernel.lean`, where the Smrčka–Středa surface primitive and
residual sea kernel are introduced.

`Resolvent/Spectral.lean` owns the model-independent side-indexed eigenvector action and squared
pure-point action of resolvents. Retarded/advanced names are public physical specializations.
Pure-point Kubo–Bastin and Středa spectral expansions consume that result rather than re-owning
resolvent algebra.

## Disorder boundary

The exact/approximate split remains explicit:

```text
Disorder/Finite
   ├──→ Disorder/Resolvent ────────────────────────────────┐
   └──→ Disorder/Moments ──→ BornCommon ──┬──→ RetardedBorn
                       │                   └──→ AdvancedBorn
                       └────────────────────────→ SCBA

Transport/Resolvent.Basic ─────────────────────→ SCBA
```

`Disorder/Finite` owns the exact finite ensemble and normalized scalar/operator averages.
`Disorder/Resolvent` owns the exact configuration-wise retarded/advanced Green operators and Dyson
identities. `Disorder/Moments` owns the canonical bounded complex-linear exact second-moment action
`C₂(X) = E[Vω X Vω]`, proves its finite-average and adjoint-compatibility properties, and owns the
separate `IsCentered` property used to cancel first-order disorder insertions.

`Disorder/BornCommon` owns only genuinely R/A-neutral algebra shared by both first-Born
specializations: centered first-order insertion cancellation, averaging of a configuration-wise
second-order expansion, the common second-order expression `G₀ + G₀ Σ G₀`, and its exact closure
error. Orientation-sensitive Dyson remainders, physical retarded/advanced self-energy names, and
closure hypotheses stay in `Disorder/RetardedBorn` and `Disorder/AdvancedBorn`. Those modules remain
siblings and must not import one another.

The Born self-energy and approximation objects use the canonical exact second moment and therefore
do not themselves require centered disorder. Centering is required only when an exact averaged
Dyson identity is reduced by cancelling the first-order contribution. SCBA uses the same canonical
`exactSecondMomentCLM` directly in its supplied fixed-point equations; there is no second covariance
function or separately supplied linearity/adjoint-compatibility assumption. The SCBA Green and
self-energy solution itself remains approximation data and is not identified with the exact
disorder average.

## AHE benchmark hierarchy

The massive-Dirac benchmark is now physically structured as

```text
Transport/AnomalousHall/MassiveDirac/
├── Model/
│   ├── Basic.lean
│   ├── CurrentBridge.lean
│   ├── Occupation.lean
│   └── Spectral.lean
├── Intrinsic/
│   ├── BerryBridge.lean
│   ├── BerrySymmetry.lean
│   ├── Response.lean
│   └── Conductivity.lean
├── Streda/
│   ├── Response.lean
│   ├── Integral.lean
│   ├── CurrentOperatorBridge.lean
│   └── Spectral.lean
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

This hierarchy is not permission for AHE to own reusable analysis. Generic band-state occupation and
Fermi-surface notions, Lorentzian kernel/tail analysis, zero-temperature occupation/Fermi-edge
weights, and regular-factor Lorentzian pole extraction live under `Transport/Analysis/` and are
consumed by the massive-Dirac specialization.

## Generic / concrete boundary

Files under generic Transport must not import `LeanCondensedMatter.SecondQuantization`. Fermionic
finite-Fock, lattice, directional-current, Fermi-state, and Peierls-contact realizations remain in
`SecondQuantization/Fermionic/Transport` and specialize the neutral owners.

`LeanCondensedMatter.Transport` must not import the concrete AHE umbrella. The project root imports
`LeanCondensedMatter.Transport` and `LeanCondensedMatter.Transport.AnomalousHall` as separate public
tracks.

Physical formula, sign, normalization, limiting-order, and approximation semantics must not change
as part of path/ownership migration.
