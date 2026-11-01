---
status: accepted
---

# Reconstruct compact self-adjoint operators on their nonzero spectral support

Index eigenvectors over the nonzero eigenspaces and use a Hilbert basis of their closed span, the orthogonal complement of the operator's kernel. Derive countability of this support from compactness rather than assuming that the ambient Hilbert space is separable.

The kernel contributes zero to the operator's action and spectral trace but may have infinite, even nonseparable, dimension. Excluding it avoids an irrelevant requirement to enumerate a basis there. The cost is explicit projection and reconstruction proofs: the supported eigenvector family is not a basis of the whole space when the kernel is nontrivial. A vectorwise convergent spectral reconstruction also does not by itself assert trace-classness or absolute summability of eigenvalues.

Evidence: [current spectral family and index](../../LeanCondensedMatter/Analysis/Operator/Spectral/EigenvectorFamily.lean) and [spectral-trace-class bundle](../../LeanCondensedMatter/Analysis/Operator/TraceClass/Spectral/Bundled.lean).

## Relation to general trace class

`SpectralTraceClass T` bundles general trace-class membership and symmetry. Compactness and
absolute summability of nonzero real eigenvalues are derived. This is a self-adjoint spectral
interface to the general trace-class theory, not the representation stored in density states.
The general complex trace agrees with the real spectral trace on this interface.

When comparing different operators, use a common Hilbert basis and explicit `HasSum` witnesses
for trace-series arguments. An equality of totalized `tsum` expressions alone does not justify
interchanging sums. Nonzero eigenspaces and their multiplicities determine the spectral sum;
the selected orthonormal vectors within each eigenspace do not change that scalar value.

For sums whose summand ignores the basis-vector index, separate the eigenvalue index from the
finite multiplicity sum rather than reindexing a dependent spectral `Sigma` type through casts;
see the [proof conventions](../conventions.md).
