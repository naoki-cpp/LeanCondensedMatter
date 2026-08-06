# Roadmap — Fredholm determinant

This note records the design boundary established by #439. It separates the operator-ideal
infrastructure already proved in the repository from the prerequisites of a general Fredholm
determinant, while choosing a first implementation slice that is already genuinely
infinite-dimensional.

## Current status

- Hilbert–Schmidt basic, inner-product, and spectral-trace comparison modules are `proved`.
- A general non-self-adjoint trace-class ideal is not implemented.
- A general Fredholm determinant is not implemented.
- The first implementation slice is the countable diagonal infinite-product target in #659.

The diagonal infinite-dimensional target is `stated`; the general trace-class target remains `idea`.

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
- finite-dimensional determinants are available through
  `Mathlib.Topology.Algebra.Module.Determinant`, including `ContinuousLinearMap.det`;
- the project audit has not found a Mathlib replacement for the repository's Hilbert–Schmidt
  package;
- the project does not rely on a Mathlib general trace-class/Schatten/Fredholm package.

`ContinuousLinearMap.det` must not be used as an infinite-dimensional determinant definition. Its
role is limited to a later compatibility theorem on finite-dimensional diagonal specializations.
The first implementation instead uses a convergent infinite product.

## First implementation slice: countable diagonal operators

Issue #659 owns the first machine-checked Fredholm determinant slice. Let

```text
d : HilbertBasis ι ℂ H
K : H →L[ℂ] H
λ : ι → ℂ
```

with countable index type `ι`, diagonalization

```text
K (d i) = λ i • d i,
```

and absolute summability

```text
Summable (fun i => ‖λ i‖).
```

The intended determinant is

```text
Det(I + K) = ∏' i, (1 + λ i).
```

This target is genuinely infinite-dimensional when `ι` is infinite. The absolute-summability
hypothesis supplies the convergence needed for the infinite product and is the diagonal analogue of
the trace-class condition.

The first slice should provide:

1. convergence of the product from `Summable (fun i => ‖λ i‖)`;
2. a definition based on `tprod`, guarded by proved `Multipliable` or `HasProd` evidence;
3. invariance under reindexing by an equivalence of index types;
4. the zero-operator value;
5. finite-support reduction to a finite product;
6. finite-dimensional compatibility with `ContinuousLinearMap.det` where the existing basis/matrix
   API supports a clean proof;
7. a kernel statement when one factor satisfies `1 + λ i = 0`.

The initial API may bundle the Hilbert basis, coefficient family, diagonalization equation, and
summability proof, or expose them as theorem parameters. The representation should be chosen for
proof stability rather than to imitate a general trace-class ideal prematurely.

## Independence boundary

Reindexing invariance is required: equivalent enumerations of the same diagonal data must give the
same determinant.

Full independence from an arbitrary choice of diagonalizing Hilbert basis is not part of the first
slice unless it follows from a separately proved uniqueness theorem for the spectral data. In
particular, the first implementation must not silently identify unrelated diagonal presentations.

## Extension path

The intended sequence is:

```text
countable diagonal trace-class data
  → diagonal compact/self-adjoint compatibility
  → normal trace-class spectral data
  → general non-self-adjoint trace-class ideal
  → general Fredholm determinant.
```

The first arrow already produces a nontrivial infinite-dimensional determinant. Later arrows widen
the operator domain and strengthen presentation independence.

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

## Completion rule

#439 can be completed once this design boundary is merged, the existing Hilbert–Schmidt results are
linked from the issue, the caveats are updated, and #659 owns the countable diagonal
infinite-dimensional implementation. A future general Fredholm issue should be opened only after
the non-self-adjoint trace-class ideal has a concrete compiled API rather than a proposed
compatibility layer.
