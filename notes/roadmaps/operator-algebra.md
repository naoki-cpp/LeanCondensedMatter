# Operator analysis (Track C)

Track C owns dimension-independent analytic infrastructure used by quantum theory, transport, and
second quantization.

## Infinite sums and spectral analysis

`Analysis/InfiniteSum/` provides reusable reindexing, fiberwise sum, and justified countable-sum
exchange tools.

`Analysis/Operator/Spectral/` provides compact self-adjoint spectral decomposition with countable
nonzero spectrum, finite multiplicities, eigenvector reconstruction, kernel completion, arbitrary
Hilbert-basis comparison, and positivity results.

These layers are physics-independent.

## Spectral trace class

`Analysis/Operator/TraceClass/` provides `ContinuousLinearMap.SpectralTraceClass` for compact
self-adjoint operators, spectral trace, positivity/additivity/scalar results, supported cyclicity,
and Hilbert-basis formulas.

This is sufficient for the current density-operator, entropy, and bounded Gibbs constructions, but it
is not a general trace-class ideal on arbitrary non-self-adjoint maps.

## Hilbert--Schmidt operators

`Analysis/Operator/HilbertSchmidt/` provides basis-independent Hilbert--Schmidt membership, adjoint
invariance, closure under bounded composition, the pairing `innerHS`, and comparison with spectral
trace on the compact self-adjoint overlap.

A general non-self-adjoint trace-class product ideal with trace norm, completeness, and general trace
remains open.

## Fredholm determinant

For absolutely summable diagonal coefficients,

```text
Fredholm.diagonalDet coeff = ∏' i, (1 + coeff i)
```

is proved with convergence, reindexing invariance, finite-support/index reductions, exact zero
characterization, and kernel consequences. The finite-dimensional diagonal specialization is proved
equal to Mathlib's ordinary determinant.

This does not yet define a Fredholm determinant for arbitrary trace-class operators. See
[`fredholm-determinant.md`](fredholm-determinant.md) for the missing general trace-class prerequisites.

## Functional calculus and bounded Dyson theory

`Analysis/FunctionalCalculus/` owns reusable bounded self-adjoint functional-calculus facts used by
Gibbs and entropy constructions.

`Analysis/Dyson/` owns generic Banach-algebra Dyson coefficients, factorial bounds, summability,
Volterra equations, uniqueness, and constant-generator exponential identification. Quantum and
SecondQuantization modules instantiate these results rather than duplicating the analytic series.

## Domain-aware and completed-space analysis

Domain-aware unbounded infrastructure is no longer wholly absent. The repository contains
`LinearPMap`-based unbounded operator tools, and the completed fermionic line provides explicit
maximal diagonal domains, dense-domain/closedness/adjoint/self-adjointness results for real diagonal
weights, bounded completed CAR operators, and product-domain/free-Hamiltonian relations.

These results do not amount to a general unbounded spectral theory. In particular, the following
remain open or only partially covered:

- a general non-self-adjoint trace-class/Schatten ideal and trace;
- unbounded self-adjoint functional calculus sufficient for general interacting Hamiltonians;
- compact-resolvent/heat-semigroup infrastructure for genuine infinite-dimensional Gibbs theory;
- completed bosonic ladder/number operator domains and analytic closure;
- general interacting completed-space Dyson theory;
- infinite-volume and thermodynamic limits.

Unbounded objects must retain explicit domains; no result should obtain them by coercing an
unbounded operator to a bounded continuous map.
