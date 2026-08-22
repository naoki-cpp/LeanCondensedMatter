# Second-quantization architecture

This note records the stable ownership and dependency boundaries of
`LeanCondensedMatter/SecondQuantization/`. Lean declarations and the durable architecture audits under
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

Particle-statistics-independent one-body current semantics are not second-quantization declarations.
They live upstream under `Analysis` and `QuantumTheory.ConservationLaw`; second-quantized layers only
supply `dGamma`, bounded-realization, lattice, and response adapters where those are genuinely needed.

## Repository-level dependency direction

The stable repository-level direction is

```text
Analysis, Combinatorics, QuantumTheory
          ↓
SecondQuantization.Common
          ↓
SecondQuantization.Fermionic, SecondQuantization.Bosonic
```

The durable CI rules are current-state dependency rules:

- `Analysis`, `Combinatorics`, and `QuantumTheory` do not import `SecondQuantization`;
- `SecondQuantization.Common` does not import `Fermionic` or `Bosonic`;
- statistics-specific layers may consume Common and upstream reusable mathematics/quantum theory.

These rules intentionally do not maintain blacklists of modules, imports, or identifiers that existed
before an earlier refactor.

## Fermionic responsibility DAG

Within the fermionic tree, reusable theory flows downstream through explicit responsibility layers:

```text
Fermionic.Algebra
      ↓
┌───────────────────────────────┐
│ Fermionic.Field               │  basis-independent/dGamma side interface
│ Fermionic.Lattice             │  lattice realization
└───────────────────────────────┘
        ↓
Fermionic.Transport             bounded/Kubo specializations
        ↓
Fermionic.Validation            terminal examples and checks
```

`Field` and `Lattice` are sibling realization layers. Reusable `Algebra` does not depend on either
realization or on downstream consumers. `Field` and `Lattice` do not depend on `Transport` or
`Validation`, and `Transport` does not depend on `Validation`.

The dependency DAG is owned centrally by
`scripts/check_fermionic_transport_validation_boundary.py`. Focused AlgebraicFock and Lattice audits
add domain-specific constraints without duplicating that graph.

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

One-body generalized current work that does not use second quantization should instead import the
appropriate `Analysis` or `QuantumTheory.ConservationLaw` leaf.

Leaf implementation files are not a compatibility surface. When a routing module ceases to represent
a reusable concept, downstream code should consume the surviving semantic owner rather than keeping a
compatibility layer solely for an old import path.

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

The two-point expansion has its own internal layer order:

```text
Semantics → Factorization → Analysis → Integration → Series
```

Lower layers must not import higher layers or their umbrella. The checker derives this from parsed
Lean imports rather than source-line regexes.

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

## Fermionic field/current boundary

The basis-independent algebraic field architecture is documented separately in
[`fermionic-field-operators.md`](fermionic-field-operators.md). The one-body/current boundary is

```text
Analysis.Operator.LinearCommutator
        ↓
Analysis.Calculus.OneBodyBalance
        ↓
Analysis.Calculus.CurrentRepresentation
        ↓
QuantumTheory.ConservationLaw
        ↓
┌───────────────────────────────┐
│ Fermionic.Field               │  dGamma generalized-quantity bridge
│ Fermionic.Lattice             │  lattice current constructions
└───────────────────────────────┘
        ↓
Fermionic.Transport
```

`Fermionic.Field` remains a narrow side interface for basis-independent density constructions and the
fermionic `dGamma` bridge. It is not a one-body transport umbrella. Generic response, resolvent,
conductivity, and Středa mathematics belongs upstream under `QuantumTheory` or other reusable owners;
`Fermionic.Transport` contains statistics/model-specific bounded adapters and physical current
response specializations.

The generic bounded-current response module must not depend on the conventional current
`1/2 {v,m}`. Conventional-current response is a downstream specialization, so non-conventional
orbital/nonlocal currents can enter through the same arbitrary-current boundary.

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

Permanent architecture CI should encode the current layer graph, canonical ownership, dimension
boundaries, and semantic safety rules. It should not accumulate a history of removed files, former
owners, or incidental proof syntax.

## CI-enforced invariants

`scripts/check_second_quantization_architecture.py` owns the repository-level SecondQuantization
boundaries:

- path-owned `Common`, `Fermionic`, and `Bosonic` declaration namespaces;
- no statistics-specific imports from `Common`;
- no `SecondQuantization` imports from `Analysis`, `Combinatorics`, or `QuantumTheory`;
- the canonical public SecondQuantization entry point.

`scripts/check_fermionic_transport_validation_boundary.py` owns the fermionic responsibility DAG.
Other focused audits own domain-specific constraints such as algebraic dimension independence,
lattice/response separation, thermal ownership, mode boundaries, density boundaries, and diagrammatic
layer ordering.

Architecture documentation should describe those durable current-state rules. Migration history
belongs in Git history and issue/PR discussion rather than permanent CI assertions.
