import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.RCLike.Lemmas

set_option linter.style.header false

/-!
# Compact rank-one operators

Generic compactness facts for rank-one continuous linear maps. These facts are shared by
the neutral diagonal-operator construction and the spectral-trace density-state layer.
-/

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [InnerProductSpace 𝕜 F]

namespace InnerProductSpace

/-- Rank-one continuous linear maps are compact. -/
theorem isCompactOperator_rankOne (x : E) (y : F) :
    IsCompactOperator (rankOne 𝕜 x y : F →L[𝕜] E) := by
  letI : ProperSpace 𝕜 := FiniteDimensional.proper_rclike 𝕜 𝕜
  rw [rankOne_def']
  exact (isCompactOperator_of_locallyCompactSpace_dom (innerSL 𝕜 y)).clm_comp
    (ContinuousLinearMap.toSpanSingleton 𝕜 x)

end InnerProductSpace
