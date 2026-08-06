# Roadmap — Fredholm determinant

This note records the design boundary established by #439. It separates the operator-ideal
infrastructure already proved in the repository from the prerequisites of a genuine
infinite-dimensional Fredholm determinant.

## Current status

- Hilbert–Schmidt basic, inner-product, and spectral-trace comparison modules are `proved`.
- A general non-self-adjoint trace-class ideal is not implemented.
- A general Fredholm determinant is not implemented.
- The first implementation slice is the explicitly finite-dimensional compatibility target in #659.

The finite-dimensional target is `stated`; the infinite-dimensional target remains `idea`.

## Existing Hilbert–Schmidt boundary

`Analysis/Operator/HilbertSchmidt/` currently provides:

- `ContinuousLinearMap.IsHilbertSchmidtWrt`, defined by summability of squared basis images;
- basis independence and the basis-independent predicate
  `ContinuousLinearMap.IsHilbertSchmidt`;
- invariance under adjoint;
- closure under bounded composition on either side;
- the basis-independent Hilbert–Schmidt pairing `innerHS`;
- agreement of `innerHS d 1 A` with `spectralTrace A` on the compact self-adjoint spectrally
  summable domain.

This is a genuine Hilbert–Schmidt layer, but it is not yet a complete Schatten-ideal package. In
particular, the repository has not packaged the product of two Hilbert–Schmidt operators as an
arbitrary non-self-adjoint trace-class operator with a general trace.

## Mathlib boundary at the pinned revision

At Mathlib `v4.31.0`:

- bounded and compact continuous linear maps are available;
- finite-dimensional determinants are available through
  `Mathlib.Topology.Algebra.Module.Determinant`, including `ContinuousLinearMap.det`;
- the project audit has not found a Mathlib replacement for the repository's Hilbert–Schmidt
  package;
- the project does not rely on a Mathlib general trace-class/Schatten/Fredholm package.

The finite-dimensional implementation must reuse `ContinuousLinearMap.det`. It must not introduce
an unrelated determinant implementation or use the determinant's fallback behavior as an
infinite-dimensional definition.

## First implementation slice

Issue #659 owns the finite-dimensional compatibility theorem. For a finite-dimensional complex
Hilbert space and bounded endomorphism `K`, the intended quantity is the ordinary determinant

```text
det (1 + K).
```

Any project wrapper must make the finite-dimensional scope explicit in its name and hypotheses.
Useful first results are:

1. compatibility with `ContinuousLinearMap.det`;
2. the zero-perturbation value;
3. exact multiplicative and conjugation identities inherited from ordinary determinant theory;
4. matrix or basis compatibility only where it adds a stable project-facing boundary.

This slice is a model and regression target for future Fredholm theory. It is not itself an
infinite-dimensional Fredholm determinant.

## Candidate general constructions

### Exterior-power series

The classical series

```text
Det(1 + K) = sum_n Tr(exteriorPower n K)
```

is structurally attractive because it supports determinant identities and trace-log expansions.
It requires completed exterior powers, trace-class estimates on exterior powers, and convergence of
the resulting scalar series. None of that infrastructure is currently present.

### Product over eigenvalues

For compact trace-class operators one may seek a product over algebraic eigenvalues with
multiplicity. This route requires non-self-adjoint compact spectral theory, algebraic multiplicity,
convergence and reindexing of infinite products, and independence from the chosen spectral
presentation. The current compact self-adjoint real-eigenvalue API is too narrow for this route.

### Finite-rank approximation

One may define finite-rank determinants and prove convergence along trace-norm approximations. This
requires a general trace norm, completeness of the trace-class ideal, density of finite-rank
operators, and independence of the approximating sequence. The repository does not yet have these
prerequisites.

## Dependency graph for a genuine Fredholm determinant

A later infinite-dimensional implementation should not begin until the following layers exist:

1. **General non-self-adjoint trace-class predicate or bundled ideal**
   - closed under adjoint;
   - closed under bounded multiplication on either side;
   - contains products of two Hilbert–Schmidt operators.
2. **Trace-class norm and completeness**
   - ideal norm estimates;
   - finite-rank density or another approximation theorem.
3. **General trace**
   - basis independence;
   - linearity and cyclicity on the valid product domain;
   - agreement with matrix trace and the existing spectral trace on overlaps.
4. **One determinant construction with convergence**
   - exterior-power series, eigenvalue product, or trace-norm completion of finite-rank
     determinants.
5. **Structural identities**
   - multiplicativity on the correct domain;
   - continuity in trace norm;
   - finite-dimensional and finite-rank compatibility.
6. **Optional logarithmic layer**
   - trace-log expansion only under explicit norm or spectral hypotheses;
   - branch choices for the complex logarithm kept explicit.

## Non-goals of the current slice

- treating `SpectralTraceClass` as a general trace-class ideal;
- defining the determinant of every compact operator;
- claiming an eigenvalue product without algebraic multiplicity and convergence;
- claiming `log Det(1 + K) = Tr log(1 + K)` without branch and convergence hypotheses;
- thermodynamic or infinite-volume determinant limits.

## Completion rule

#439 can be completed once this design boundary is merged, the existing Hilbert–Schmidt results are
linked from the issue, the caveats are updated, and #659 owns the finite-dimensional implementation.
A future general Fredholm issue should be opened only after the non-self-adjoint trace-class ideal
has a concrete compiled API rather than a proposed compatibility layer.
