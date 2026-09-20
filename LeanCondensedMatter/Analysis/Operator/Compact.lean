import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap

set_option linter.style.header false

/-!
# Compact rank-one operators

Generic compactness facts for bounded operators on inner-product spaces. These facts are shared by
the neutral diagonal-operator construction and the spectral-trace density-state layer.
-/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

namespace ContinuousLinearMap

/-- Rank-one operators on an inner-product space are compact. -/
theorem isCompactOperator_rankOne (x y : H) :
    IsCompactOperator (InnerProductSpace.rankOne ℂ x y : H →L[ℂ] H) := by
  rw [InnerProductSpace.rankOne_def']
  exact (isCompactOperator_of_locallyCompactSpace_dom (innerSL ℂ y)).clm_comp
    (ContinuousLinearMap.toSpanSingleton ℂ x)

end ContinuousLinearMap
