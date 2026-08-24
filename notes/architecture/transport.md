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
│   ├── LorentzianKernel.lean
│   ├── LorentzianPole.lean
│   └── ZeroTemperatureOccupation.lean
├── KuboBastin/
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
    ├── Born.lean
    ├── AdvancedBorn.lean
    └── SCBA.lean
```

The stable public grouping modules are `Transport.Core`, `Transport.Resolvent`,
`Transport.KuboBastin`, `Transport.Streda`, and `Transport.Disorder`. The project-level
`LeanCondensedMatter.Transport` imports those five groups. The retired `Transport.Foundations`,
`Transport.ResolventAPI`, and historical flat Core/Resolvent leaf modules were removed after
repository-wide consumer audits showed no remaining imports.

Other historical flat leaf paths remain temporarily as forwarding modules so downstream consumers
can be migrated incrementally. They must not contain declarations. `scripts/check_transport_hierarchy.py`
enforces that the remaining compatibility paths forward to their canonical owners.

## Semantic Kubo–Bastin / Středa boundary

`KuboBastin/Occupation.lean` and `KuboBastin/CommonEnergy.lean` remain on the Kubo–Bastin side of
the boundary: they build occupation-resolved and common-energy representations but do not define a
Středa surface or sea term. Genuine Středa ownership begins at `Streda/OperatorKernel.lean`, where
the Smrčka–Středa surface primitive and residual sea kernel are introduced.

`Resolvent/Spectral.lean` owns the model-independent eigenvector action of retarded/advanced
resolvents. Both finite Kubo–Bastin and Středa spectral expansions consume that result rather than
re-owning resolvent algebra.

## Disorder boundary

The exact/approximate split remains explicit:

```text
                   ┌→ Disorder/Resolvent ─┐
Disorder/Finite ───┤                       ├→ Disorder/Born
                   └→ Disorder/Moments ────┤
                                           └→ Disorder/AdvancedBorn

Disorder/Finite + Resolvent
              ↓
         Disorder/SCBA
```

`Disorder/Moments` and `Disorder/Resolvent` are sibling exact owners. Advanced Born must not depend
on retarded Born merely to reuse moments. SCBA remains independent of the first-Born closure owner.

## AHE benchmark hierarchy

The massive-Dirac benchmark is now physically structured as

```text
Transport/AnomalousHall/MassiveDirac/
├── Model/
│   ├── Basic.lean
│   ├── CurrentBridge.lean
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
The remaining old flat `MassiveDirac*` and `MassiveDiracBastin*` files are compatibility forwarders
only; retired pole-error shims have already been removed.

This hierarchy is not permission for AHE to own reusable analysis. Generic Lorentzian kernel/tail
analysis, zero-temperature occupation/Fermi-edge weights, and regular-factor Lorentzian pole
extraction now live under `Transport/Analysis/` and are consumed by the massive-Dirac specialization.

## Generic / concrete boundary

Files under generic Transport must not import `LeanCondensedMatter.SecondQuantization`. Fermionic
finite-Fock, lattice, directional-current, Fermi-state, and Peierls-contact realizations remain in
`SecondQuantization/Fermionic/Transport` and specialize the neutral owners.

`LeanCondensedMatter.Transport` must not import the concrete AHE umbrella. The project root imports
`LeanCondensedMatter.Transport` and `LeanCondensedMatter.Transport.AnomalousHall` as separate public
tracks.

Physical formula, sign, normalization, limiting-order, and approximation semantics must not change
as part of path/ownership migration.
