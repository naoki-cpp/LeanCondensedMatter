---
status: accepted
---

# Keep operator ideals and determinants within proved domains

Keep the project-local Hilbert–Schmidt API scoped to its proved basis-independent predicate, inner product, adjoint invariance, and bounded-composition closure. Do not infer that an arbitrary product of two Hilbert–Schmidt operators belongs to the current compact self-adjoint spectral trace-class model: those notions have different domains and require a general trace-class ideal to connect them.

Define an infinite-dimensional Fredholm determinant only on data with an explicit convergent product, currently absolutely summable diagonal coefficients. Use the ordinary linear-map determinant only for finite-dimensional compatibility. A general non-self-adjoint trace-class ideal, trace norm and completeness, cyclic trace, or presentation-independent determinant requires those foundations first.

Evidence: [Hilbert–Schmidt API](../../LeanCondensedMatter/Analysis/Operator/HilbertSchmidt/Basic.lean), [Hilbert–Schmidt pairing](../../LeanCondensedMatter/Analysis/Operator/HilbertSchmidt/InnerProduct.lean), [diagonal Fredholm determinant](../../LeanCondensedMatter/Analysis/Operator/Fredholm/Diagonal.lean), and [Fredholm determinant roadmap](../../notes/roadmaps/fredholm-determinant.md).

## Historical evidence

[Issue #694](https://github.com/naoki-cpp/LeanCondensedMatter/issues/694) makes the diagonal zero-set theorem conditional on the same absolute-summability data as the determinant itself: the convergent product vanishes exactly when one factor is zero, and the operator consequence supplies a basis-vector kernel witness. The result reuses the infinite-product APIs and does not assign spectral meaning to an unconstrained totalized product.

[Issue #677](https://github.com/naoki-cpp/LeanCondensedMatter/issues/677) confirms the finite-dimensional bridge is a theorem, not the determinant's definition: express `1 + diagonalOp` as a diagonal matrix in the basis, then reuse Mathlib's matrix determinant and the finite-product specialization. No parallel finite determinant API is needed.

[Issue #659](https://github.com/naoki-cpp/LeanCondensedMatter/issues/659) fixes the first genuinely infinite-dimensional determinant API at explicit absolutely summable diagonal coefficient data. It defines a convergent `tprod`, proves equivalence-reindexing invariance and kernel consequences for `1 + HilbertBasis.diagonalOp`, and leaves basis independence beyond that transport, spectral-trace/trace-log identities, and arbitrary trace-class determinants unclaimed. Finite-dimensional `det` agreement is a separate compatibility slice.

[Issue #439](https://github.com/naoki-cpp/LeanCondensedMatter/issues/439) established this boundary explicitly. The Hilbert–Schmidt layer is independently useful, but arbitrary products cannot be routed through the compact self-adjoint spectral trace API. The implemented first Fredholm slice is the convergent product `∏' i, (1 + coeff i)` under absolute summability, with reindexing, zero characterization, and finite-dimensional determinant compatibility. The issue leaves general trace-class and determinant theory as separate work rather than implying it from the diagonal slice.
