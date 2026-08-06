# Roadmap — Operator analysis (Track C)

Track C owns dimension-independent analytic infrastructure used by quantum theory and second
quantization. See [the project roadmap](../roadmap.md),
[the density-state architecture](../architecture/quantum-density-theory.md), and the
[Fredholm determinant roadmap](fredholm-determinant.md).

## Infinite-sum infrastructure

Status: `proved` for the current reusable APIs.

`Analysis/InfiniteSum/` contains the sum-reindexing and fiberwise tools used throughout spectral,
thermal, and combinatorial proofs. Important components include:

- finite products of summable series indexed by `Finsupp`;
- fiberwise `HasSum` and `tsum` rearrangements;
- justified exchange of countable sums under summability or nonnegativity hypotheses.

These theorems are analysis utilities and must not depend on quantum or second-quantization modules.

## Compact self-adjoint spectral tools

Status: `proved`.

The project provides a spectral decomposition for compact self-adjoint bounded operators using an
index of nonzero real eigenvalues with finite multiplicity. The API includes:

- an orthonormal eigenvector family;
- countability of the nonzero spectral index;
- reconstruction of the operator from its eigenvectors;
- identification of the orthogonal complement of the nonzero spectral subspace with the kernel;
- extension and comparison lemmas for arbitrary Hilbert bases;
- positivity of eigenvalues for positive operators.

The implementation is organized under `Analysis/Operator/Spectral/` and is the common foundation for
spectral trace, density operators, entropy, and diagonal constructions.

## Spectral trace-class operators

Status: `proved` for compact self-adjoint operators.

`Analysis/Operator/TraceClass/` defines:

- summability of nonzero real eigenvalues with multiplicity;
- bundled `ContinuousLinearMap.SpectralTraceClass` data;
- spectral trace;
- trace nonnegativity for positive operators;
- scalar and additive linearity;
- cyclicity in the supported composition setting;
- computation from arbitrary Hilbert bases;
- diagonal positive and scalar constructions;
- bounds for sums over orthonormal families.

This theory is sufficient for the canonical `QuantumTheory.DensityOperator`, entropy operators, and
bounded Gibbs-state results.

It is not a general operator ideal on arbitrary non-self-adjoint maps. In particular, the project
does not yet expose a trace for every product `ρA`; density-state expectation is defined separately
from the state’s spectral decomposition and agrees with matrix trace in finite dimensions.

## Hilbert–Schmidt operators

Status: `proved` for the current basic, inner-product, and trace modules.

`Analysis/Operator/HilbertSchmidt/` provides:

- a basis-defined squared-norm summability predicate;
- basis independence and the basis-independent `IsHilbertSchmidt` predicate;
- adjoint invariance;
- closure under bounded composition on either side;
- the basis-independent Hilbert–Schmidt pairing `innerHS`;
- comparison of `innerHS d 1 A` with `spectralTrace A` on the compact self-adjoint spectrally
  summable overlap.

This is a separate analytic layer and is not used as an alternative public density-state
representation. It also does not yet package the product of two Hilbert–Schmidt operators as an
arbitrary non-self-adjoint trace-class operator with a general trace.

Remaining work, if required by a concrete theorem, includes a more complete ideal API, composition
closure with broader trace-class operators, and systematic comparison with singular-value-based
Schatten classes.

## Fredholm determinant

Status: `stated` for an explicitly finite-dimensional compatibility slice; `idea` for a genuine
infinite-dimensional determinant.

The design gate is recorded in [the Fredholm determinant roadmap](fredholm-determinant.md). The first
implementation issue is #659 and must reuse Mathlib's finite-dimensional
`ContinuousLinearMap.det` on `1 + K` under explicit finite-dimensional hypotheses.

A genuine Fredholm determinant remains blocked on:

- a non-self-adjoint trace-class ideal;
- ideal norm and completeness;
- a general trace agreeing with matrix and spectral traces on overlaps;
- a convergent exterior-power, eigenvalue-product, or finite-rank approximation construction;
- determinant identities on the correctly stated domain.

No current theorem should use the finite-dimensional determinant as an implicit infinite-dimensional
definition or claim trace-log identities without explicit convergence and logarithm-branch
hypotheses.

## Continuous functional calculus

Status: `proved` for the bounded self-adjoint use cases in the repository.

`Analysis/FunctionalCalculus/` supplies eigenvector evaluation and compactness-preservation lemmas
used to construct:

- `gibbsOp Hop β = exp (-β Hop)`;
- `entropyOp ρ = -ρ log ρ`.

Consumers may need to enable Mathlib’s base continuous-functional-calculus instance locally. The
functional-calculus layer remains independent of the physical interpretation of the resulting
operators.

## Bounded Dyson–Volterra analysis

Status: `proved`.

`Analysis/Dyson/` owns the generic Banach-algebra Dyson coefficients, factorial bounds, summability,
Volterra equation, uniqueness, and constant-generator exponential identification.
`QuantumTheory/BoundedDyson.lean` is the bounded-operator specialization. Finite
SecondQuantization modules reuse these theorems rather than defining separate analytic series.

## Unbounded and completed-space boundary

Status: `idea`.

The following require a new domain-aware theory:

- unbounded self-adjoint Hamiltonians;
- compact resolvent and heat-semigroup hypotheses;
- genuinely infinite-dimensional Gibbs states;
- creation, annihilation, and number operators on completed Fock space;
- KMS statements with explicit operator domains;
- thermodynamic and infinite-volume limits.

These cannot be obtained by treating unbounded operators as bounded continuous maps.

## Remaining operator analysis

- General trace-class and Schatten ideals for non-self-adjoint operators.
- Product/ideal closure sufficient for a general trace `Tr(ρA)` in infinite dimensions.
- The finite-dimensional Fredholm compatibility slice in #659.
- General Fredholm determinants and logarithmic determinant expansions after the ideal prerequisites.
- Unbounded spectral and functional calculus with domain control.
- Completed infinite-mode Fock representations and closability/self-adjointness results.
