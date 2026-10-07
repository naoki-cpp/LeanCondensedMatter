# Analysis inventory against Mathlib 4.34

Current mapping between project analysis infrastructure and the repository-pinned Mathlib revision
`v4.34.1`. This document describes the present API, not the sequence of refactors that produced it.

## Classification

- **Mathlib-owned:** the project uses the Mathlib declaration directly.
- **Thin project corollary:** a small wrapper crosses a useful scalar, coercion, or namespace boundary.
- **Project-specific:** no pinned-Mathlib declaration provides the required theorem or packaging.
- **Upstream candidate:** general-purpose project code that may be suitable for Mathlib.

## Mathlib-owned foundations

The project uses Mathlib directly for:

- bounded and compact continuous linear maps;
- compactness under bounded composition through `IsCompactOperator.comp_clm` and `IsCompactOperator.clm_comp`;
- positivity under adjoint conjugation through `ContinuousLinearMap.IsPositive.conj_adjoint`;
- finite-dimensional matrix trace and orthonormal-basis formulas;
- finite-dimensional determinants through `ContinuousLinearMap.det`;
- infinite products through `HasProd`, `Multipliable`, and `tprod`;
- convergence of `∏' i, (1 + coeff i)` from `Summable (fun i => ‖coeff i‖)` through
  `multipliable_one_add_of_summable`;
- self-adjoint operator spectrum and eigenspaces;
- continuous functional calculus on C⋆-algebras;
- Bochner integration and interval integrals;
- power series and elementary complex/real analysis;
- general incidence algebras and Möbius inversion;
- polynomial evaluation on eigenvectors through `Module.End.aeval_apply_of_mem_apply_eq_smul`;
- scalar eigenspace transport through `Module.End.eigenspace_div`.

Project modules must not duplicate these APIs under compatibility names.

## Thin retained corollaries

The following remain because their statements match recurring project boundaries:

| Project declaration | Mathlib basis | Purpose |
|---|---|---|
| `cfc_apply_eigenvector` | continuous functional calculus and spectral mapping | Evaluate a continuous scalar function on an eigenvector. |
| `HilbertBasis.hasSum_norm_sq_inner` | Hilbert-basis Parseval identities | Provide the norm-squared form used by spectral trace proofs. |
| `tsum_fiberwise_eq_of_summable` | product-sum rearrangement and `HasSum.prod_fiberwise` | Package an absolutely summable fiberwise exchange. |

## Project-specific infinite-sum infrastructure

`Analysis/InfiniteSum/` owns:

- finite products of summable series indexed by `Finsupp`;
- geometric product specializations;
- fiberwise `HasSum` and `tsum` rearrangements used by spectral and thermal proofs.

These modules are physics-independent.

The diagonal Fredholm slice reuses Mathlib's infinite-product convergence and reindexing APIs
directly. No new generic infinite-product theorem was needed for the current vertical slice.

## Project-specific compact spectral packaging

Mathlib supplies eigenspaces and compact-operator primitives but not the complete package required by
the repository. `Analysis/Operator/Spectral/` provides:

- the nonzero real eigenvalue index with multiplicity;
- a countable orthonormal eigenvector family;
- reconstruction of compact self-adjoint operators;
- kernel/orthogonal-complement decomposition;
- Hilbert-basis comparison theorems.

## Trace-class APIs

`ContinuousLinearMap.IsTraceClass T` is the project-local general non-self-adjoint trace-class
membership predicate. It is defined by Hilbert--Schmidt membership of
`CFC.sqrt (CFC.abs T)` and is equivalent, in every Hilbert basis, to summability of the
nonnegative diagonal of `|T|`.

The compact self-adjoint spectral specialization remains

```lean
ContinuousLinearMap.SpectralTraceClass T
```

which bundles general trace-class membership and symmetry. Compactness is derived from
`IsTraceClass.isCompact`, and summability of the nonzero real eigenvalues is derived from the
compact self-adjoint characterization. Its associated `spectralTrace` is the real spectral sum.

`Analysis/Operator/TraceClass/General.lean` owns general membership and the Hilbert-basis criterion.
`Analysis/Operator/TraceClass/Norm.lean` owns the canonical basis-independent real trace norm,
its Hilbert-basis diagonal formula, and the absolute diagonal formula induced by a left polar
factor. `Analysis/Operator/TraceClass/Factorization/Basic.lean` owns the trace-norm-independent
characterization of trace class as `T = A† B` with Hilbert--Schmidt factors.
`Analysis/Operator/TraceClass/Factorization/Norm.lean` owns the general bound
`‖T‖₁ ≤ (‖A‖²_HS + ‖B‖²_HS) / 2` and a factorization with both squared
Hilbert--Schmidt norms equal to the trace norm. `TraceClass/Trace.lean`
owns the direct diagonal `Summable`/`HasSum`/`tsum` API, basis independence, and the canonical
complex trace; there is no separate basis-relative trace-series wrapper. `TraceClass/Compact.lean`
derives compactness directly from the factorization layer.
`Analysis/Operator/TraceClass/Ops/Basic.lean` owns additive/scalar/adjoint closure, bounded left/right
ideal closure, and complex-trace linearity. `TraceClass/Ops/Norm.lean` owns trace-norm identities,
the left/right operator-norm bounds, the triangle inequality, and the trace-versus-trace-norm bound. `TraceClass/AdjointConjugation.lean` owns adjoint-conjugation closure and trace invariance derived
from general cyclicity.
`Analysis/Operator/TraceClass/Spectral/` owns spectral summability, the bundled self-adjoint
specialization, spectral trace identities, and spectral equality criteria. `Spectral/Bundled.lean` also exposes the compact self-adjoint characterizations
of general trace-class membership, trace norm, and complex trace.

`Analysis/Operator/Diagonal.lean` owns the neutral Hilbert-basis diagonal construction, including
the absolutely summable rank-one series, basis action, and compactness.

The basis-independent general complex trace is `IsTraceClass.trace`. For self-adjoint
trace-class operators, `IsTraceClass.realTrace` transports that proved-real scalar losslessly to
`ℝ` through `Complex.selfAdjointEquiv`. The real-valued `spectralTrace` remains the
eigenvalue-sum representation for compact self-adjoint operators rather than the canonical trace API.
On the overlap, `IsTraceClass.trace_eq_spectralTrace` identifies the general complex trace with the
coercion of that spectral sum to `ℂ`.

## Hilbert–Schmidt API

`Analysis/Operator/HilbertSchmidt/` contains the project-local Hilbert–Schmidt predicate,
basis-independence results, adjoint and bounded-composition closure, compactness, inner product, and
trace reconciliation used by current proofs. No pinned-Mathlib replacement covers the same package.

The package supplies the neutral norm-square series used by general trace-class membership together
with the Hilbert--Schmidt inner product used to prove absolute convergence and basis independence of
the general complex trace. The general trace-class layer builds on this package for adjoint and
bounded-composition closure, the left/right ideal norm bounds, and cyclicity of the canonical
complex trace; completeness remains a separate downstream result.

## Diagonal Fredholm determinant API

`Analysis/Operator/Fredholm/Diagonal.lean` provides the project-specific interpretation of Mathlib's
infinite product as a Fredholm determinant for explicit diagonal data:

```lean
Fredholm.diagonalDet coeff = ∏' i, (1 + coeff i).
```

The module reuses Mathlib for convergence, reindexing of `tprod`, finite-product reduction, and
nonvanishing of absolutely convergent products. Project-specific theorems connect the coefficient
family to `HilbertBasis.diagonalOp`, including the action of `1 + diagonalOp b coeff` on basis vectors
and the nonzero kernel vector produced by a coefficient equal to `-1`.

This is a genuine infinite-dimensional diagonal slice. It is not a determinant on arbitrary compact,
normal, or trace-class operators and is not independent of unrelated diagonal presentations.

`Mathlib.Topology.Algebra.Module.Determinant` provides `ContinuousLinearMap.det` as the determinant of
the underlying linear endomorphism. It is appropriate only for future finite-dimensional
compatibility results and is not used as the infinite-dimensional definition.

A general Fredholm determinant still requires trace-class approximation/completeness and a
convergent presentation-independent determinant construction. The scoped dependency graph is
recorded in `docs/roadmaps/fredholm-determinant.md`.

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

- trace-class approximation/completeness;
- a complete Schatten hierarchy;
- a Fredholm determinant on general trace-class operators;
- basis independence for unrelated diagonal presentations without spectral uniqueness;
- unbounded spectral/functional calculus with domains;
- completed infinite-mode Fock-space operator theory.

These are future analysis targets rather than gaps to be hidden by compatibility wrappers.
