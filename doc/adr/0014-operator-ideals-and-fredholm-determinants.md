---
status: accepted
---

# Keep operator ideals and determinants within proved domains

Keep the project-local Hilbert–Schmidt API scoped to its proved basis-independent predicate, inner product, adjoint invariance, and bounded-composition closure. Products of Hilbert–Schmidt operators can feed the general non-self-adjoint trace-class ideal through the proved factorization API, but they must not be routed through the compact self-adjoint spectral trace-class model without the additional spectral hypotheses.

Construct Hilbert-basis diagonal operators in the neutral `Analysis.Operator.Diagonal` layer from absolutely summable coefficients; keep their series, basis action, compactness, and positivity facts independent of trace-class structure. Spectral-trace-class membership and trace formulas are downstream adapters that add their own hypotheses. Fredholm results consume the neutral diagonal operator construction directly, while `SecondQuantization.Common.diagonalOperator` remains a distinct representation with its own semantics.

Define an infinite-dimensional Fredholm determinant only on data with an explicit convergent product, currently absolutely summable diagonal coefficients. Use the ordinary linear-map determinant only for finite-dimensional compatibility. General non-self-adjoint trace-class membership, its canonical trace and trace norm, bounded ideal closure, left/right ideal norm bounds, and trace cyclicity are available; a determinant on arbitrary trace-class operators still requires approximation/completeness and a convergent presentation-independent construction.

Evidence: [Hilbert–Schmidt API](../../LeanCondensedMatter/Analysis/Operator/HilbertSchmidt/Basic.lean), [Hilbert–Schmidt pairing](../../LeanCondensedMatter/Analysis/Operator/HilbertSchmidt/InnerProduct.lean), [diagonal Fredholm determinant](../../LeanCondensedMatter/Analysis/Operator/Fredholm/Diagonal.lean), and [Fredholm determinant roadmap](../../notes/roadmaps/fredholm-determinant.md).

## Historical evidence

[PR #2808](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2808) locates finite-dimensional compatibility beside the diagonal Fredholm determinant it specializes. The theorem remains a public bridge to Mathlib's ordinary determinant; proof-only helpers do not create a second module or determinant API. `Analysis.Operator` imports the determinant leaf directly after the declaration-free `Operator.Fredholm` forwarder is removed.

[Issue #2525](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2525), implemented by [PR #2538](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2538), moves Hilbert-basis diagonal operator construction and its summability, basis-action, and compactness facts into the neutral Analysis operator owner. Positivity and spectral-trace statements remain adapters, and Fredholm and density/Gibbs consumers reuse the same operator series without compatibility aliases or merging the separate `Common.diagonalOperator` representation. Current sources: [neutral diagonal operator](../../LeanCondensedMatter/Analysis/Operator/Diagonal.lean), [spectral-trace adapter](../../LeanCondensedMatter/Analysis/Operator/TraceClass/Spectral/Diagonal.lean), and [diagonal Fredholm determinant](../../LeanCondensedMatter/Analysis/Operator/Fredholm/Diagonal.lean).

[Issue #2457](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2457) adds Simon's trace-ideal and Fredholm-determinant reference to the annotated [analytic-foundations bibliography](../../notes/references.md). Its role is to specify the operator-ideal assumptions needed before claiming a general trace-class determinant; it does not broaden the implemented absolutely-summable diagonal determinant or the finite-dimensional compatibility theorem. The issue remains open as a literature-acquisition task.

[Issue #694](https://github.com/naoki-cpp/LeanCondensedMatter/issues/694) makes the diagonal zero-set theorem conditional on the same absolute-summability data as the determinant itself: the convergent product vanishes exactly when one factor is zero, and the operator consequence supplies a basis-vector kernel witness. The result reuses the infinite-product APIs and does not assign spectral meaning to an unconstrained totalized product.

[Issue #677](https://github.com/naoki-cpp/LeanCondensedMatter/issues/677) confirms the finite-dimensional bridge is a theorem, not the determinant's definition: express `1 + diagonalOp` as a diagonal matrix in the basis, then reuse Mathlib's matrix determinant and the finite-product specialization. No parallel finite determinant API is needed.

[Issue #659](https://github.com/naoki-cpp/LeanCondensedMatter/issues/659) fixes the first genuinely infinite-dimensional determinant API at explicit absolutely summable diagonal coefficient data. It defines a convergent `tprod`, proves equivalence-reindexing invariance and kernel consequences for `1 + HilbertBasis.diagonalOp`, and leaves basis independence beyond that transport, spectral-trace/trace-log identities, and arbitrary trace-class determinants unclaimed. Finite-dimensional `det` agreement is a separate compatibility slice.

[Issue #439](https://github.com/naoki-cpp/LeanCondensedMatter/issues/439) established this boundary explicitly. The Hilbert–Schmidt layer is independently useful, but arbitrary products cannot be routed through the compact self-adjoint spectral trace API. The implemented first Fredholm slice is the convergent product `∏' i, (1 + coeff i)` under absolute summability, with reindexing, zero characterization, and finite-dimensional determinant compatibility. The issue leaves general trace-class and determinant theory as separate work rather than implying it from the diagonal slice.
