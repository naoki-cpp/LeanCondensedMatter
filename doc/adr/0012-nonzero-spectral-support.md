---
status: accepted
---

# Reconstruct compact self-adjoint operators on their nonzero spectral support

Index eigenvectors over the nonzero eigenspaces and use a Hilbert basis of their closed span, the orthogonal complement of the operator's kernel. Derive countability of this support from compactness rather than assuming that the ambient Hilbert space is separable.

The kernel contributes zero to the operator's action and spectral trace but may have infinite, even nonseparable, dimension. Excluding it avoids an irrelevant requirement to enumerate a basis there. The cost is explicit projection and reconstruction proofs: the supported eigenvector family is not a basis of the whole space when the kernel is nontrivial. A vectorwise convergent spectral reconstruction also does not by itself assert trace-classness or absolute summability of eigenvalues.

Evidence: [current spectral family and index](../../LeanCondensedMatter/Analysis/Operator/Spectral/EigenvectorFamily.lean) and [spectral-trace-class bundle](../../LeanCondensedMatter/Analysis/Operator/TraceClass/Spectral/Bundled.lean).

## Historical evidence

[Issue #281](https://github.com/naoki-cpp/LeanCondensedMatter/issues/281) explains the present bundle: spectral summability alone was renamed `HasSummableRealEigenvalues`, the scalar sum `spectralTrace`, and compactness, symmetry, and summability were collected in `SpectralTraceClass`. Storing this bundle directly in density operators removed duplicate hypotheses and compatibility-only bridges. The narrower names prevent a restricted self-adjoint spectral construction from being mistaken for a general trace-class ideal.

[PR #16](https://github.com/naoki-cpp/LeanCondensedMatter/pull/16) compared different operators through a common Hilbert basis instead of identifying their individual eigenbases. Its summation argument required `HasSum` witnesses and a justified interchange of sums; an equality involving totalized `tsum` alone would not supply those convergence obligations. The shared-basis bridge is the reusable boundary, while closure assumptions on the operators remain explicit.

[PR #15](https://github.com/naoki-cpp/LeanCondensedMatter/pull/15) records a concrete trade-off when transporting spectral sums: directly reindexing the dependent eigenvector `Sigma` type caused kernel timeouts, so the proof split the sum into a nondependent eigenvalue index and a finite multiplicity sum. When the summand ignores the basis-vector index, that decomposition removes unnecessary dependent casts while retaining eigenspace multiplicity. This supports the present [convention against directly reindexing dependent spectral indices](../../notes/conventions.md), without fixing an incidental proof script.

[PR #13](https://github.com/naoki-cpp/LeanCondensedMatter/pull/13) defined the spectral trace and proved positivity without first developing Hilbert–Schmidt operators. It also noted that a scalar eigenvalue sum does not automatically supply linearity or cyclicity across different operators, whose spectral index types differ. The current construction may use additional bridges; the historical choice was to unblock the compact self-adjoint trace, not to exclude Hilbert–Schmidt theory permanently.

[PR #12](https://github.com/naoki-cpp/LeanCondensedMatter/pull/12) expressed spectral summability using absolute nonzero eigenvalues with eigenspace multiplicity. Those values depend on the eigenspaces and their dimensions, not on the selected orthonormal vectors within them. This avoids unnecessary basis-choice data in the scalar predicate. Its historical name `IsTraceClass` must not be read as a general Schatten-ideal definition: the present public `SpectralTraceClass` bundle explicitly includes compactness and symmetry as well as summability.

[PR #8](https://github.com/naoki-cpp/LeanCondensedMatter/pull/8) explicitly excluded the zero eigenspace for this reason. [PR #9](https://github.com/naoki-cpp/LeanCondensedMatter/pull/9) derived countability from finiteness above each positive eigenvalue threshold. [PR #10](https://github.com/naoki-cpp/LeanCondensedMatter/pull/10) identified the supported subspace, and [PR #11](https://github.com/naoki-cpp/LeanCondensedMatter/pull/11) supplied its Hilbert basis and a `HasSum` reconstruction of the operator's action. These are separate obligations; the earlier PR titles alone do not establish all of them.
