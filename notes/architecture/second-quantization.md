# Second-quantization architecture

This note records the stable ownership and dependency boundaries of
`LeanCondensedMatter/SecondQuantization/`. Lean declarations and the architecture audits under
`scripts/` are the source of truth; this document explains the intended shape of those checks.

## Ownership

Second-quantization declarations are owned by exactly one of three statistics layers:

```text
SecondQuantization.Common
SecondQuantization.Fermionic
SecondQuantization.Bosonic
```

Files under `SecondQuantization/Common/` own statistics-independent constructions that still depend
on second-quantized semantics: occupation/Fock infrastructure, imaginary-time and thermal interfaces,
finite operator integration, diagram data, component decompositions, shuffles, and other reusable
many-body constructions.

Files under `Fermionic/` and `Bosonic/` own statistics-specific algebra, signs, occupation rules,
Hamiltonians, convergence assumptions, physical specializations, and final physics-facing theorems.
A declaration should not remain in a statistics-specific layer merely because that is where its proof
was first developed.

## Dependency direction

The stable dependency direction is

```text
Analysis, Combinatorics
          ↓
SecondQuantization.Common
          ↓
SecondQuantization.Fermionic, SecondQuantization.Bosonic
```

`Analysis/` and `Combinatorics/` must not import `SecondQuantization`. `Common` must not import
fermionic or bosonic modules. Statistics-specific layers may consume Common and upstream reusable
mathematics.

The architecture audit also checks path-owned namespaces and rejects removed compatibility imports
and legacy ownership paths.

## Public import boundary

The full public entry point is

```lean
import LeanCondensedMatter.SecondQuantization
```

Responsibility-specific developments should prefer the narrowest public leaf umbrella, for example

```lean
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics
import LeanCondensedMatter.SecondQuantization.Fermionic.Transport
```

Leaf implementation files are not a compatibility surface. When a one-use routing module is removed,
downstream code should migrate to the surviving semantic owner rather than preserving the old import.

## Diagrammatics boundary

The current diagrammatic architecture separates reusable combinatorics from statistics-specific
amplitudes.

```text
Combinatorics
  finite partitions / pairings / cumulants
          ↓
SecondQuantization.Common.Diagrammatics
  ordered data / components / reassembly / shuffles / simplex products
          ↓
SecondQuantization.Fermionic.Diagrammatics
  fermionic pair values / signs / Wick amplitudes / Dyson expansions
          ↓
physics-facing connected theorems
```

Common owns component and shuffle structure when no fermionic sign or energy data is required.
Fermionic modules should call those results directly instead of exposing parameter-substitution or
proof-routing wrappers.

Public declarations should correspond to reusable mathematical structure or physics-facing endpoints.
Proof-only reindexing, transport, uniqueness, and one-use bridge theorems should normally be private,
local, or inlined when doing so reduces code without hiding a genuine domain concept.

## Current linked-cluster endpoints

The finite-mode fermionic partition-function line has both formal and analytic linked-cluster
endpoints. The canonical formal endpoint is

```lean
SecondQuantization.Fermionic.
  factorial_mul_coeff_dysonFormalLogPartitionFunction_eq_sum_connectedAmplitude
```

and the finite-dimensional analytic endpoint is

```lean
SecondQuantization.Fermionic.
  iteratedDeriv_log_normalizedAnalyticPartitionFunction_eq_sum_connectedAmplitude
```

The external-leg line has also reached the finite-mode two-point endpoint

```lean
SecondQuantization.Fermionic.
  vacuumNormalizedTwoPointDysonSeries_eq_connectedTwoPointDysonSeries
```

in `TwoPointDiagramExpansion/CauchySeries.lean`. This means the next correlation-function target is
higher-point/source-insertion structure, not re-proving the two-point linked-cluster identity.

## Fermionic algebra, lattice, transport, and validation

The basis-independent algebraic field architecture is documented separately in
[`fermionic-field-operators.md`](fermionic-field-operators.md). Its downstream responsibility flow is

```text
Fermionic.Algebra
      ↓
Fermionic.Lattice
      ↓
Fermionic.Transport
      ↓
Fermionic.Validation
```

`Fermionic.Field` remains a narrow side interface for basis-independent density constructions rather
than a transport umbrella. Generic response, resolvent, conductivity, and Středa mathematics belongs
upstream under `QuantumTheory` or other reusable owners; Fermionic.Transport contains the
statistics/model-specific adapters and physical current specializations.

## Bosonic boundary

Bosonic algebraic and free thermal results may reuse Common infrastructure, but finite fermionic trace
arguments must not be transferred merely because the mode type is finite. A finite bosonic mode set
still has an infinite occupation basis. Product-domain closure, summability, KMS identities, operator
integration, and Dyson convergence therefore remain explicit analytic obligations of the bosonic
line.

## Refactoring rule

Architecture cleanup should optimize for semantic ownership and API size, not theorem-name length.
Good deletion targets are dead declarations, one-use public wrappers, and modules that contain only a
proof-routing theorem whose proof can be absorbed by its sole consumer with a net code reduction.
Rename-only churn is not an architecture improvement by itself.

When a reusable concept survives, keep it at the narrowest authoritative owner. When only a proof path
survives, keep that path private/local rather than turning it into public API.

## CI-enforced invariants

`scripts/check_second_quantization_architecture.py` enforces the core structural rules, including:

- path-owned `Common`, `Fermionic`, and `Bosonic` declaration namespaces;
- no statistics-specific imports from `Common`;
- no `SecondQuantization` imports from `Analysis` or `Combinatorics`;
- absence of removed compatibility modules/imports;
- absence of legacy fermionic identifiers and ownership paths.

Other focused audits enforce mode-boundary and theorem-catalog constraints. Documentation should be
updated when those checks or the canonical public boundaries change; prose must not preserve an
architecture that CI has already removed.
