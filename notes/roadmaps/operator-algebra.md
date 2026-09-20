# Operator analysis (Track C)

Track C owns dimension-independent analytic infrastructure used by quantum theory, transport, and
second quantization.

## Fixed-sign commutator algebra

On the pinned Mathlib v4.33.1 (`0df444a360eaa60ab8c11dca51a86af692955474`), the ordinary
associative commutator is available through the Lie bracket,
`⁅A, B⁆ = A * B - B * A` (`LieRing.of_associative_ring_bracket`), with `Module.End` multiplication
identified with composition by `Module.End.mul_eq_comp`. The pinned API survey found no
`zetaCommutator`, q-commutator, or fixed-scalar twisted-commutator family matching
`A ∘ B - ζ • (B ∘ A)`.

Accordingly, `Analysis/Operator/ZetaCommutator.lean` owns the minimal representation-independent
`LinearMap.zetaCommutator` extension. Ordinary commutator APIs remain semantic `ζ = 1`
specializations, while second-quantization code selects `ζ` through `Statistics.zetaInt`. Re-check
this ownership after Mathlib upgrades.

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

The neutral Hilbert-basis diagonal operator construction is owned by
`Analysis/Operator/Diagonal.lean`; the TraceClass diagonal modules only adapt it to positivity and
spectral-trace-class results.

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
Volterra equations, uniqueness, and constant-generator exponential identification. Its canonical
analytic seam is `Dyson.BoundedInteraction`, which keeps the weak identity estimate `‖1‖ ≤ 1`, a
nonnegative majorant, and the interaction norm bound explicitly scoped to `[0, β]`;
`Dyson.ContinuousBoundedInteraction` adds the global continuity required by the Volterra theory.
Neither structure asserts a bound outside the finite interval or strengthens the ambient norm
classes. Quantum and SecondQuantization modules instantiate these hypotheses rather than duplicating
the analytic proof wiring.

## Domain-aware and completed-space analysis

Domain-aware unbounded infrastructure is no longer wholly absent. The repository contains
`LinearPMap`-based unbounded operator tools, and the completed fermionic line provides explicit
maximal diagonal domains, dense-domain/closedness/adjoint/self-adjointness results for real diagonal
weights, bounded completed CAR operators, and product-domain/free-Hamiltonian relations.

These results do not amount to a general unbounded spectral theory. On the pinned Mathlib
v4.33.1 (`0df444a360eaa60ab8c11dca51a86af692955474`), `LinearPMap` provides the domain-aware
adjoint, dense-domain consequences of self-adjointness, and closedness of self-adjoint operators.
Neither the pinned Mathlib API nor the current project supplies a general unbounded self-adjoint
functional calculus, projection-valued spectral measure calculus, semibounded quadratic-form
package tied to `LinearPMap`, or a strongly continuous positive heat-semigroup construction.
The project-local resolvent/Cayley/Stone line constructs strongly continuous unitary evolution from
a self-adjoint `LinearPMap` without such a functional calculus; it does not define
`exp (-β H)`.
Its consumer-facing endpoint is routed through
`Analysis/Operator/Unbounded/StoneEvolution.lean`; resolvent approximation, convergence, and
domain-transport proofs remain implementation-stage machinery behind that route.

For genuine infinite-dimensional Gibbs theory, the first general equilibrium boundary is therefore
**heat-operator first** rather than Hamiltonian first. The quantum layer may accept, at a fixed
`β > 0`, a bounded positive heat operator `Kβ` together with explicit spectral trace-class data
and nonzeroness. Positivity plus spectral trace class and nonzeroness imply strictly positive trace,
and `DensityOperator.normalizePositive` is the canonical normalization boundary. The statement that
`Kβ = exp (-β H)` for a semibounded unbounded self-adjoint Hamiltonian belongs to
the upstream domain-aware analysis layer and must retain the Hamiltonian domain and lower-bound
assumptions explicitly. A future heat-semigroup or unbounded functional-calculus implementation can
supply that bridge without changing the density-state normalization API.

The countable pure-point construction remains the spectral-data specialization, not a second
general interface. Its compatibility theorem with the heat-operator boundary should require a
Hilbert basis `b` and energies `E` for which the supplied heat operator satisfies

```text
Kβ (b i) = exp (-β E i) • b i
```

The quantum Gibbs layer uses this basis action and spectral-trace-class data to derive Boltzmann
summability, identifies the bundled heat trace with the pure-point partition function, and identifies
`DensityOperator.normalizePositive Kβ ...` with `purePointGibbsDensityOperator b E β`. A general
spectral-data-first boundary should wait for a genuine spectral-measure/functional-calculus
API rather than extending the pure-point representation beyond what it proves.

The following remain open or only partially covered:

- a general non-self-adjoint trace-class/Schatten ideal and trace;
- the Hamiltonian-to-heat bridge for semibounded unbounded self-adjoint operators;
- unbounded self-adjoint functional calculus or equivalent heat-semigroup infrastructure;
- compact-resolvent criteria implying trace-class heat operators;
- completed bosonic ladder/number operator domains and analytic closure;
- general interacting completed-space Dyson theory;
- infinite-volume and thermodynamic limits.

Unbounded objects must retain explicit domains; no result should obtain them by coercing an
unbounded operator to a bounded continuous map.
