# Fredholm determinant roadmap

The repository has a genuine infinite-dimensional determinant for absolutely summable diagonal data.
PhyslibAlpha provides a general trace-class ideal and trace API, and the project's positive spectral
trace class has a trace-preserving bridge to it. A Fredholm determinant on that general ideal is not
yet defined.

## Proved diagonal boundary

For

```text
coeff : ι → ℂ
Summable (fun i => ‖coeff i‖),
```

`Analysis/Operator/Fredholm/Diagonal.lean` defines

```text
Fredholm.diagonalDet coeff = ∏' i, (1 + coeff i).
```

The public results include convergence of the product, reindexing invariance, finite-support and
finite-index reductions, nonvanishing when every factor is nonzero, and

```text
Fredholm.diagonalDet coeff = 0 ↔ ∃ i, coeff i = -1.
```

For a diagonal operator, determinant zero therefore produces a nonzero basis vector in the kernel of
`1 + diagonalOp b coeff`.

`Analysis/Operator/Fredholm/Diagonal.lean` also proves agreement with Mathlib's ordinary
determinant on finite diagonal specializations. `ContinuousLinearMap.det` is not used as an
infinite-dimensional definition.

## Operator-analysis boundary

The existing Hilbert--Schmidt layer provides basis independence, adjoint invariance, bounded
composition, and the basis-independent pairing `innerHS`. PhyslibAlpha's [TraceClass modules](https://github.com/leanprover-community/physlib/tree/b840c857d3b5b87cd3a0e58eac7696b7bdb2fe17/PhyslibAlpha/ProbabilisticTheory/HilbertSpace/TraceClass)
provide a general non-self-adjoint trace-class ideal, trace norm, trace, and product APIs. The local
spectral bundle bridges positive operators to that API; it does not classify arbitrary operators.

`ContinuousLinearMap.SpectralTraceClass` remains a compact self-adjoint spectral construction; it is
not a general predicate for arbitrary non-self-adjoint operators.

Reindexing invariance of `diagonalDet` does not imply independence from arbitrary unrelated
diagonalizing Hilbert bases. Such a statement needs spectral uniqueness on the relevant operator
class.

## Requirements for a general Fredholm determinant

A determinant over PhyslibAlpha's trace-class operators requires, at minimum:

1. an explicit choice between the operator predicate `ProbabilisticTheory.IsTraceClass` and the
   bundled `ProbabilisticTheory.TraceClass` type, using the library's adjoint and product laws;
2. analytic bounds for the chosen construction using the library's trace norm and Banach structure;
3. trace and cyclicity results applied only on the product domains supported by the library;
4. a convergent determinant formula, such as an exterior-power series or eigenvalue product with
   multiplicity control;
5. structural results such as finite-rank compatibility, continuity, and multiplicativity under
   explicit hypotheses.

Trace-log identities additionally require explicit convergence and complex-logarithm branch
conditions.

## Open work

- characterize invertibility of `1 + diagonalOp b coeff` under exact diagonal hypotheses;
- relate the diagonal determinant to the existing spectral trace on a proved overlap;
- define the determinant over PhyslibAlpha's trace-class API and prove the required convergence and
  finite-rank compatibility;
- extend the determinant beyond diagonal or otherwise explicitly controlled spectral data.

The current API must not be broadened by finite-dimensional fallback behavior or by silently treating
compactness, Hilbert--Schmidt membership, or spectral trace class as general trace class.
