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

Move declarations that still live directly in `SecondQuantization` into exactly one of:

```lean
SecondQuantization.Common
SecondQuantization.Fermionic
SecondQuantization.Bosonic
```

The migration must update every in-repository caller in the same PR. No root-namespace forwarding
aliases should remain.

### R2 — Common ownership and wrapper removal

Remove fermionic files whose public declarations are line-for-line specializations of Common APIs.
The first confirmed targets are:

- `Fermionic/Perturbation/DysonExpansion.lean`, which forwards `Common.dysonCoeff`, its recursion
  theorems, matrix-coefficient continuity, and `Common.dysonTruncation`;
- the generic portions of `Fermionic/Perturbation/ContinuousDyson.lean`, which forward continuous
  finite-operator and analytic Dyson declarations.

Physics-facing corollaries may remain fermionic, but they should state their results directly using
the authoritative Common construction.

### R3 — fermionic canonical names

Replace statistic suffixes with namespace ownership. Confirmed examples include:

```text
FockSpaceFermionic     -> Fermionic.FockSpace
FermionOccupation      -> Fermionic.Occupation
ContinuousFockSpaceFermionic -> Fermionic.ContinuousFockSpace
ContinuousFermionOperator    -> Fermionic.ContinuousOperator
```

The precise migration should be done as a repository-wide atomic change because these names are used
through algebra, thermal theory, perturbation theory, and diagrammatics.

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
