# Roadmap — Fredholm determinant

This note records the design boundary established by #439. It separates the operator-ideal
infrastructure already proved in the repository from the prerequisites of a general Fredholm
determinant, while choosing a first implementation slice that is already genuinely
infinite-dimensional.

## Current status

- Hilbert–Schmidt basic, inner-product, and spectral-trace comparison modules are `proved`.
- The countable diagonal infinite-product slice is `proved` in
  `Analysis/Operator/Fredholm/Diagonal.lean`.
- Finite-dimensional agreement with Mathlib's ordinary determinant is `proved` in
  `Analysis/Operator/Fredholm/FiniteDimensional.lean`.
- A general non-self-adjoint trace-class ideal is not implemented.
- A general Fredholm determinant is not implemented.

The diagonal infinite-dimensional target and its finite-dimensional compatibility are `proved`;
the general trace-class target remains `idea`.

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
- infinite products are available through the general `HasProd`, `Multipliable`, and `tprod` APIs;
- `multipliable_one_add_of_summable` proves convergence of `∏' i, (1 + coeff i)` from
  `Summable (fun i => ‖coeff i‖)`;
- finite-dimensional determinants are available through
  `Mathlib.Topology.Algebra.Module.Determinant`, including `ContinuousLinearMap.det`;
- the project audit has not found a Mathlib replacement for the repository's Hilbert–Schmidt
  package;
- the project does not rely on a Mathlib general trace-class/Schatten/Fredholm package.

`ContinuousLinearMap.det` is not used as an infinite-dimensional determinant definition. It is used
only by the proved finite-dimensional compatibility theorem for diagonal specializations. The
infinite-dimensional slice itself remains defined by a convergent infinite product.

## Implemented slice: countable diagonal operators

For explicit coefficient data

```text
coeff : ι → ℂ
```

with absolute summability

```text
Summable (fun i => ‖coeff i‖),
```

`Fredholm.diagonalDet` is defined by

```text
Fredholm.diagonalDet coeff = ∏' i, (1 + coeff i).
```

This target is genuinely infinite-dimensional when `ι` is infinite. The absolute-summability
hypothesis supplies the convergence needed for the infinite product and is the diagonal analogue of
the trace-class condition.

The public API currently provides:

- `Fredholm.diagonalDet_multipliable`: convergence of the defining product;
- `Fredholm.diagonalDet_reindex`: invariance under an equivalence of index types;
- `Fredholm.diagonalDet_zero`: the zero-coefficient value;
- `Fredholm.diagonalDet_eq_finsetProd`: finite-support reduction;
- `Fredholm.diagonalDet_fintype`: reduction to the ordinary finite product on a finite index type;
- `Fredholm.diagonalDet_ne_zero`: nonvanishing when every factor is nonzero;
- `HilbertBasis.one_add_diagonalOp_apply_basis`: diagonal action of
  `1 + diagonalOp b coeff`;
- `HilbertBasis.one_add_diagonalOp_has_nonzero_kernel_vector_of_coeff_eq_neg_one`: a coefficient
  equal to `-1` produces a nonzero kernel vector;
- `Fredholm.diagonalDet_eq_det_one_add_diagonalOp`: agreement with
  `ContinuousLinearMap.det (1 + diagonalOp b coeff)` when the index type is finite.

The determinant is defined from explicit coefficient data rather than bundled with a Hilbert basis
or operator. The operator theorems connect that coefficient-level definition to the repository's
existing `HilbertBasis.diagonalOp` construction without pretending that a general trace-class ideal
already exists.

## Finite-dimensional compatibility

`Analysis/Operator/Fredholm/FiniteDimensional.lean` converts a finite `HilbertBasis` to its ordinary
basis, identifies the matrix of `1 + diagonalOp b coeff` as
`Matrix.diagonal (fun i => 1 + coeff i)`, and applies Mathlib's `LinearMap.det_toMatrix` and
`Matrix.det_diagonal` theorems. Thus both the infinite-product definition and the ordinary
determinant reduce to the same finite product.

This theorem is compatibility only. It does not redefine `Fredholm.diagonalDet`, weaken its analytic
boundary, or turn `ContinuousLinearMap.det` into an infinite-dimensional determinant.

## Independence boundary

Reindexing invariance is proved: equivalent enumerations of the same diagonal data give the same
determinant.

Full independence from an arbitrary choice of diagonalizing Hilbert basis is not part of the current
slice. It requires a separately proved uniqueness theorem for the spectral data. In particular, the
implementation does not silently identify unrelated diagonal presentations.

## Extension path

The intended sequence is:

```text
countable diagonal trace-class data
  → diagonal compact/self-adjoint compatibility
  → normal trace-class spectral data
  → general non-self-adjoint trace-class ideal
  → general Fredholm determinant.
```

The first step now provides a nontrivial infinite-dimensional determinant, together with agreement
with ordinary determinants on finite diagonal specializations. Later steps widen the operator domain
and strengthen presentation independence.

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
multiplicity. The diagonal slice is the first controlled instance of this construction. Extending it
to arbitrary normal or non-normal operators requires spectral uniqueness, algebraic multiplicity,
convergence and reindexing of infinite products, and independence from the chosen spectral
presentation. The current compact self-adjoint real-eigenvalue API is too narrow for the general
non-self-adjoint route.

### Finite-rank approximation

One may define finite-rank determinants and prove convergence along trace-norm approximations. This
requires a general trace norm, completeness of the trace-class ideal, density of finite-rank
operators, and independence of the approximating sequence. The repository does not yet have these
prerequisites.

## Dependency graph for a general Fredholm determinant

The diagonal slice does not require the full graph below. A determinant on arbitrary trace-class
operators does require it:

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
- claiming an eigenvalue product for non-normal operators without algebraic multiplicity and
  convergence;
- claiming basis independence beyond proved reindexing or spectral-uniqueness theorems;
- claiming `log Det(1 + K) = Tr log(1 + K)` without branch and convergence hypotheses;
- regularized determinants such as `det₂`;
- thermodynamic or infinite-volume determinant limits.

## Remaining extensions after #659 and #677

The diagonal determinant and its finite-dimensional determinant compatibility are implemented.
Further extensions should be added only when cleanly supported:

- a converse relating determinant zero to a `-1` coefficient;
- invertibility of `1 + diagonalOp b coeff` under exact diagonal bounded-inverse hypotheses;
- comparison with the existing spectral trace on a self-adjoint overlap.

The current slice must not be broadened by weakening hypotheses or by using a finite-dimensional
fallback outside its valid domain.
