# Fredholm determinant roadmap

The repository currently has a genuine infinite-dimensional determinant for absolutely summable
diagonal data, but not a general Fredholm determinant on arbitrary trace-class operators.

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
composition, a basis-independent norm-square series on Hilbert--Schmidt operators, and the pairing
`innerHS`. General non-self-adjoint trace-class membership is defined by Hilbert--Schmidt membership
of `sqrt(|T|)`; its canonical real trace norm and basis-independent complex trace are available.
Membership is closed under adjoint and bounded multiplication, and the general operator-norm-weighted
left/right trace-norm bounds and cyclicity of the canonical complex trace are available.
Completeness/approximation required by Fredholm theory remains open.

`ContinuousLinearMap.SpectralTraceClass` remains a distinct compact self-adjoint spectral
construction and does not replace the general non-self-adjoint trace-class ideal.

Reindexing invariance of `diagonalDet` does not imply independence from arbitrary unrelated
diagonalizing Hilbert bases. Such a statement needs spectral uniqueness on the relevant operator
class.

## Requirements for a general Fredholm determinant

A determinant on arbitrary trace-class operators requires, at minimum:

1. a general non-self-adjoint trace-class ideal closed under adjoint and bounded multiplication;
2. a trace-class norm with the completeness/approximation results needed by the chosen construction;
3. a convergent determinant construction, such as an exterior-power series, eigenvalue product with
   multiplicity control, or trace-norm completion of finite-rank determinants;
4. structural results such as finite-rank compatibility, continuity, and multiplicativity under
   explicit hypotheses.

Trace-log identities additionally require explicit convergence and complex-logarithm branch
conditions.

## Open work

- characterize invertibility of `1 + diagonalOp b coeff` under exact diagonal hypotheses;
- relate the diagonal determinant to the existing spectral trace on a proved overlap;
- complete trace-class approximation/completeness;
- extend the determinant beyond diagonal or otherwise explicitly controlled spectral data.

The current API must not be broadened by finite-dimensional fallback behavior or by silently treating
compactness, Hilbert--Schmidt membership, or spectral trace class as general trace class.
