import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Semantics.PairContraction

set_option linter.style.header false

/-!
# Regularity of fixed-leg pair contractions

This module owns analytic regularity of the semantic pair-contraction API. The contraction and
standard-leg transport themselves remain in `PairContraction`.
-/

namespace SecondQuantization
namespace Fermionic

open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- For every fixed pair of standard two-point legs, the density-state contraction is globally
continuous in the ambient interaction-time assignment. -/
theorem continuous_orderedTwoPointLegPairContraction
    {n : ℕ} (ε : Mode → ℝ) (β : ℝ) (i j : Mode) (τ τ' : ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (x y : OrderedTwoPointLeg n) :
    Continuous (fun σ : Fin n → ℝ =>
      orderedTwoPointLegPairContraction ε β i j τ τ' q σ x y) := by
  rcases x with x | x <;> rcases y with y | y <;>
    simp only [orderedTwoPointLegPairContraction, orderedTwoPointLegField,
      orderedTwoPointLegTime, orderedTwoPointLegFieldLabel, timedFieldPairContraction_eq] <;>
    fun_prop

end Fermionic
end SecondQuantization
