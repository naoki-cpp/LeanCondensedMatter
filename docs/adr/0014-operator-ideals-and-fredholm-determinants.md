---
status: accepted
---

# Keep operator ideals and determinants within proved domains

Keep the project-local Hilbert–Schmidt API scoped to its proved basis-independent predicate, inner product, adjoint invariance, and bounded-composition closure. Products of Hilbert–Schmidt operators can feed the general non-self-adjoint trace-class ideal through the proved factorization API. The self-adjoint spectral specialization should be introduced only when spectral statements are actually needed; compactness itself is now derived from general trace-class membership.

Construct Hilbert-basis diagonal operators in the neutral `Analysis.Operator.Diagonal` layer from absolutely summable coefficients; keep their series, basis action, compactness, and positivity facts independent of trace-class structure. Spectral-trace-class membership and trace formulas are downstream adapters that add their own hypotheses. Fredholm results consume the neutral diagonal operator construction directly, while `SecondQuantization.Common.diagonalOperator` remains a distinct representation with its own semantics.

Define an infinite-dimensional Fredholm determinant only on data with an explicit convergent product, currently absolutely summable diagonal coefficients. Use the ordinary linear-map determinant only for finite-dimensional compatibility. General non-self-adjoint trace-class membership, its canonical trace and trace norm, bounded ideal closure, left/right ideal norm bounds, and trace cyclicity are available; a determinant on arbitrary trace-class operators still requires approximation/completeness and a convergent presentation-independent construction.

For the diagonal determinant, absolute summability is also the domain of its zero-set theorem:
the convergent product vanishes exactly when a factor vanishes, yielding a basis-vector kernel
witness for `1 + diagonalOp`. Finite-dimensional agreement is a theorem about the same determinant,
proved through the diagonal matrix representation; it is not a second determinant definition.
Reindexing invariance alone does not establish independence from arbitrary diagonalizing bases.

Evidence: [Hilbert–Schmidt API](../../LeanCondensedMatter/Analysis/Operator/HilbertSchmidt/Basic.lean), [Hilbert–Schmidt pairing](../../LeanCondensedMatter/Analysis/Operator/HilbertSchmidt/InnerProduct.lean), [diagonal Fredholm determinant](../../LeanCondensedMatter/Analysis/Operator/Fredholm/Diagonal.lean), and [Fredholm determinant roadmap](../roadmaps/fredholm-determinant.md).
