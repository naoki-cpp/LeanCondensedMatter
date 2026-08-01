# SecondQuantization canonical-API refactor

This document is the migration map for issue #345. The refactor is deliberately breaking:
compatibility aliases, forwarding modules, duplicate specializations, and replaced import paths are
removed rather than retained.

## Canonical public structure

```text
LeanCondensedMatter.SecondQuantization
├── Common
│   ├── Algebra
│   ├── ImaginaryTime
│   ├── Thermal
│   ├── Perturbation
│   └── Diagrammatics
├── Fermionic
│   ├── Algebra
│   ├── ImaginaryTime
│   ├── Thermal
│   ├── Perturbation
│   └── Diagrammatics
└── Bosonic
    ├── Algebra
    ├── ImaginaryTime
    ├── Thermal
    └── Diagrammatics
```

The repository-wide import is:

```lean
import LeanCondensedMatter.SecondQuantization
```

Responsibility-specific code may import a leaf umbrella such as
`LeanCondensedMatter.SecondQuantization.Fermionic.Algebra`. The former exact umbrella imports
`LeanCondensedMatter.SecondQuantization.Common`, `.Fermionic`, and `.Bosonic` are removed.

## Dependency direction

The permitted direction is:

```text
Analysis, Combinatorics
          ↓
SecondQuantization.Common
          ↓
SecondQuantization.Fermionic, SecondQuantization.Bosonic
```

Consequently:

- `Common/` must not import `Fermionic/` or `Bosonic/`;
- `Analysis/` and `Combinatorics/` must not import `SecondQuantization/`;
- statistics-specific modules may specialize Common declarations, but must not duplicate generic
  proofs merely to preserve an old name.

The CI architecture check in `scripts/check_second_quantization_architecture.py` enforces the parts
of this boundary that are already migrated.

## Completed structural packages

### Canonical entry point

PR #346 added `LeanCondensedMatter.SecondQuantization`, changed the repository root to import it, and
removed the three exact compatibility umbrella files.

### Bosonic algebra layout

PR #351 removed the `Bosonic/Foundations/` and `Bosonic/OperatorAlgebra/` split. Bosonic occupation,
Fock-space, ladder-operator, CCR, exchange, grading, and number-operator modules now live under
`Bosonic/Algebra/`.

### Common declaration namespaces

The remaining path-owned declarations in the root `SecondQuantization` namespace now live under
`SecondQuantization.Common`:

- `Common.Statistics` and its exchange-sign API;
- `Common.modeCount`;
- the quartic-leg indexing equivalences and projections in `Common.Diagrammatics.Leg`.

`Combinatorics.Pairing.weight` remains in `Combinatorics` intentionally because it extends the
combinatorial pairing type with a physics-supplied weight. The namespace audit records this as the
single explicit cross-namespace extension.

### Discrete fermionic Dyson ownership

The discrete finite-basis coefficient is now owned only by `Common.dysonCoeff`. The former
`Fermionic/Perturbation/DysonExpansion.lean` forwarding module and root `SecondQuantization.dysonCoeff`
name are removed. Fermionic verification, partition-series, and diagrammatic results specialize the
Common construction explicitly with `fermionEnergy ε`.

The architecture guard rejects reintroduction of the deleted module or import path.

### Continuous fermionic Dyson ownership

The finite-dimensional continuous and analytic Dyson constructions are now also owned only by
`SecondQuantization.Common`. The former `Fermionic/Perturbation/ContinuousDyson.lean` forwarding
module is removed. The analytic fermionic partition function states its specialization directly in
terms of:

- `Common.continuousInteractingHamiltonian (fermionEnergy ε)`;
- `Common.continuousDiagonalEvolution (fermionEnergy ε)`;
- `Common.analyticDysonEvolution (fermionEnergy ε)`;
- `Common.continuousDiagonalEvolution_neg_mul_analyticDysonEvolution_eq_exp`.

The architecture guard rejects reintroduction of this deleted module or import path as well.

### Fermionic namespace and core types

All declaration-bearing modules under `SecondQuantization/Fermionic/` now live in
`SecondQuantization.Fermionic`. The core algebraic types match the bosonic naming scheme through
namespace ownership:

```text
Fermionic.Occupation
Fermionic.FockSpace
Fermionic.vacuum
Fermionic.particleNumber
```

The former root names are removed without compatibility aliases, and the architecture guard rejects
both legacy identifiers and declaration-bearing fermionic files outside the canonical namespace.

### Analytic finite-mode fermionic line

The analytic connection is already proved; it is not a pending milestone. In particular:

- `hasSum_dysonTraceCoeff_eq_analyticDysonPartitionFunction` identifies the Dyson trace series with
  the genuine finite-dimensional interacting partition function;
- `hasFPowerSeriesAt_analyticDysonPartitionFunction` packages those coefficients as the Taylor
  series at zero coupling;
- `analyticAt_analyticNormalizedLogPartitionFunction_zero` proves analyticity of the selected local
  logarithm branch;
- `iteratedDeriv_analyticNormalizedLogPartitionFunction_eq_factorial_mul_formalCoeff` identifies
  analytic logarithmic derivatives with the existing formal logarithm coefficients;
- `iteratedDeriv_log_normalizedAnalyticPartitionFunction_eq_sum_connectedAmplitude` is the analytic
  connected-diagram theorem.

These results remain finite-mode and finite-dimensional. They do not imply completed-space,
unbounded-operator, infinite-mode, or thermodynamic-limit statements.

## Remaining migration packages

### R1 — declaration namespaces

Complete. Every declaration owned by a `Common`, `Fermionic`, or `Bosonic` module is now in the
matching namespace. The CI namespace audit rejects future path/namespace mismatches and
statistic-encoded declaration names. The only allowlisted exception is the intentional extension
`Combinatorics.Pairing.weight`.

### R2 — Common ownership and wrapper removal

The confirmed discrete and continuous Dyson forwarding modules are removed. Continue auditing the
remaining fermionic perturbation and diagrammatic modules for declarations whose implementation is
only parameter substitution into a Common construction.

Physics-facing corollaries may remain fermionic, but they should state their results directly using
the authoritative Common construction.

### R3 — fermionic canonical names

The repository-wide namespace move and the `Occupation` / `FockSpace` core-type migration are
complete. Continue auditing statistic-encoded names only where the suffix carries no physical or
mathematical distinction beyond ownership. Keep genuinely physics-facing terminology when removing
it would make the API less clear.

### R4 — bosonic convergence boundary

Keep bosonic algebra and free thermal results under the canonical hierarchy, but do not create a
false finite-basis `Perturbation` layer. A bosonic perturbation umbrella should be added only after a
summability-aware Gibbs functional and compatible operator-integration interface exist.

### R5 — perturbation and diagrammatics consolidation

Make the analytic finite-mode fermionic partition function and analytic linked-cluster theorem the
public endpoint. Formal coefficient machinery remains valuable as implementation infrastructure,
but module names and documentation should not present the analytic connection as unfinished.

The long quartic Wick component stack should be regrouped only where a file boundary exposes proof
internals rather than a reusable domain concept.

### R6 — documentation and final validation

Before closing #345:

- update the main SecondQuantization roadmap and capability matrix;
- list every removed import and renamed declaration;
- reject all migrated legacy paths in CI;
- run `lake build --wfail`, the no-`sorry` check, and Theorem Catalog;
- verify the dependency direction recorded above.

## Migration discipline

Each PR should satisfy all of the following:

1. one coherent ownership or naming change;
2. every internal caller migrated in the same change;
3. no compatibility shim for the replaced API;
4. unchanged mathematical signs, normalization, coupling powers, factorial conventions, and
   amplitudes unless a separate theorem change is explicitly reviewed;
5. full repository CI before merge.
