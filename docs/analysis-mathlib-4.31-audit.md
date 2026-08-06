# Analysis inventory against Mathlib 4.31

Current mapping between project analysis infrastructure and the repository-pinned Mathlib revision
`v4.31.0`. This document describes the present API, not the sequence of refactors that produced it.

## Classification

- **Mathlib-owned:** the project uses the Mathlib declaration directly.
- **Thin project corollary:** a small wrapper crosses a useful scalar, coercion, or namespace boundary.
- **Project-specific:** no pinned-Mathlib declaration provides the required theorem or packaging.
- **Upstream candidate:** general-purpose project code that may be suitable for Mathlib.

## Mathlib-owned foundations

The project uses Mathlib directly for:

- bounded and compact continuous linear maps;
- finite-dimensional matrix trace and orthonormal-basis formulas;
- finite-dimensional determinants through `ContinuousLinearMap.det`;
- self-adjoint operator spectrum and eigenspaces;
- continuous functional calculus on C⋆-algebras;
- Bochner integration and interval integrals;
- power series and elementary complex/real analysis;
- general incidence algebras and Möbius inversion.

Project modules must not duplicate these APIs under compatibility names.

## Thin retained corollaries

The following remain because their statements match recurring project boundaries:

| Project declaration | Mathlib basis | Purpose |
|---|---|---|
| `Polynomial.aeval_apply_eigenvector` | polynomial evaluation on eigenvectors | Connect real polynomials, complex operators, and continuous linear maps. |
| `cfc_apply_eigenvector` | continuous functional calculus and spectral mapping | Evaluate a continuous scalar function on an eigenvector. |
| `ContinuousLinearMap.eigenspace_smul` | `Module.End.eigenspace_div` | Express eigenspaces of scalar multiples in the bounded-operator API. |
| `HilbertBasis.hasSum_norm_sq_inner` | Hilbert-basis Parseval identities | Provide the norm-squared form used by spectral trace proofs. |
| `tsum_fiberwise_eq_of_summable` | product-sum rearrangement and `HasSum.prod_fiberwise` | Package an absolutely summable fiberwise exchange. |

## Project-specific infinite-sum infrastructure

`Analysis/InfiniteSum/` owns:

- finite products of summable series indexed by `Finsupp`;
- geometric product specializations;
- fiberwise `HasSum` and `tsum` rearrangements used by spectral and thermal proofs.

These modules are physics-independent.

## Project-specific compact spectral packaging

Mathlib supplies eigenspaces and compact-operator primitives but not the complete package required by
the repository. `Analysis/Operator/Spectral/` provides:

- the nonzero real eigenvalue index with multiplicity;
- a countable orthonormal eigenvector family;
- reconstruction of compact self-adjoint operators;
- kernel/orthogonal-complement decomposition;
- Hilbert-basis comparison theorems.

## Spectral trace-class API

The project’s canonical operator hypothesis is

```lean
ContinuousLinearMap.SpectralTraceClass T
```

It bundles compactness, symmetry, and summability of nonzero real eigenvalues. The associated trace
is a spectral trace for compact self-adjoint operators.

`Analysis/Operator/TraceClass/` provides:

- bundled and unbundled spectral summability;
- trace computation from arbitrary Hilbert bases;
- positivity, scalar linearity, additivity, and supported cyclicity;
- diagonal, positive, and scalar constructions;
- orthonormal-family trace bounds.

This is not Mathlib’s general trace-class operator ideal and must not be described as a trace on all
non-self-adjoint trace-class maps.

## Hilbert–Schmidt API

`Analysis/Operator/HilbertSchmidt/` contains the project-local Hilbert–Schmidt predicate,
basis-independence results, adjoint and bounded-composition closure, inner product, and trace
reconciliation used by current proofs. No pinned-Mathlib replacement covers the same package.

The package does not yet supply a general non-self-adjoint trace-class ideal or a trace on every
product of two Hilbert–Schmidt operators.

## Determinant boundary

`Mathlib.Topology.Algebra.Module.Determinant` provides `ContinuousLinearMap.det` as the determinant of
the underlying linear endomorphism. This is the correct API for the explicitly finite-dimensional
compatibility slice in #659.

The project must not treat that finite-dimensional determinant as a general Fredholm determinant.
A future infinite-dimensional implementation still requires a non-self-adjoint trace-class ideal,
a trace norm and completeness theory, a convergent determinant construction, and proofs of the
structural identities on the valid domain. The scoped dependency graph is recorded in
`notes/roadmaps/fredholm-determinant.md`.

## Ordered-simplex and Dyson analysis

The ordered-simplex integral and shuffle modules remain project-specific. Their dependency direction
is from combinatorial shuffle data toward analysis, never from generic combinatorics into physical
modules.

`Analysis/Dyson/` owns the generic Banach-algebra Dyson recursion, factorial estimates, convergence,
Volterra equation, uniqueness, and constant-generator exponential theorem. Finite and quantum
specializations reuse this layer.

## Continuous functional calculus applications

The project-specific eigenvector and compactness lemmas support:

- the entropy operator `-ρ log ρ`;
- the Gibbs operator `exp (-βH)`;
- the Peierls–Bogoliubov inequality.

The base Mathlib continuous-functional-calculus instance may need to be enabled locally in consuming
modules.

## Upstream candidates

Current general-purpose candidates include:

- `Finsupp.hasSum_prod_nonneg`;
- `Finsupp.hasSum_prod`;
- `Finsupp.hasSum_prod_geometric`;
- `tsum_fiberwise_eq_of_summable`;
- `HilbertBasis.hasSum_norm_sq_inner`.

Each candidate must be rechecked against the then-current Mathlib API before submission.

## Remaining technical debt

`Analysis/InfiniteSum/FinsuppProduct.lean` contains finite-cardinality induction proofs that use an
unbounded heartbeat setting. Before upstreaming or broadening this API:

1. make the proofs elaborate under a finite heartbeat budget;
2. isolate expensive reindexing steps;
3. minimize imports;
4. retain the geometric result as a corollary of the general product theorem.

## Current boundaries

The repository does not yet provide:

- a general non-self-adjoint trace-class ideal;
- a complete Schatten hierarchy;
- an infinite-dimensional Fredholm determinant;
- unbounded spectral/functional calculus with domains;
- completed infinite-mode Fock-space operator theory.

These are future analysis targets rather than gaps to be hidden by compatibility wrappers.
