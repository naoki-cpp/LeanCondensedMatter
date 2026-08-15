import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.ComponentPairing
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.ComponentOrderedSimplex
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.Amplitude

set_option linter.style.header false

/-!
# Component-local fermionic pair values

Statistics-independent component leg embeddings, pairing compatibility, and flattened-leg ordering
live in `SecondQuantization.Common`. This file contains only the fermionic operator and pair-value
compatibility specialized to those common embeddings.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} {N : ℕ}

section Fermionic

variable [LinearOrder Mode]

/-- A global ordered leg at a component-embedded position equals the corresponding ordered leg of
its restricted component diagram. -/
private theorem orderedQuarticLegOperator_componentOrderedLeg
    (ε : Mode → ℝ) {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (τ : Fin S.card → ℝ) (B : d.componentPartition.parts)
    (p : Fin (2 * (2 * (B : Finset (Fin N)).card))) :
    orderedQuarticLegOperator ε d (d.assembleVertexOrder orders shuffle) τ
        (d.componentOrderedLeg shuffle B p) =
      orderedQuarticLegOperator ε (d.restrictComponent B.2) (orders B)
        (d.componentTimeAssignment shuffle τ B) p := by
  unfold orderedQuarticLegOperator quarticLegOperatorForSequence
  simp only [d.orderedQuarticLegEquiv_componentOrderedLeg,
    Common.QuarticDiagram.componentTimeAssignment_apply]
  rw [d.restrictComponent_vertexLabel_componentOrder orders shuffle B]

variable [Fintype Mode]

/-- Pair values agree after embedding both component-local ordered legs into the assembled global
ordered-leg enumeration. -/
theorem orderedQuarticPairValue_componentOrderedLeg (ε : Mode → ℝ) (β : ℝ)
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (τ : Fin S.card → ℝ) (B : d.componentPartition.parts)
    (a b : Fin (2 * (2 * (B : Finset (Fin N)).card))) :
    orderedQuarticPairValue ε β d (d.assembleVertexOrder orders shuffle) τ
        (d.componentOrderedLeg shuffle B a) (d.componentOrderedLeg shuffle B b) =
      orderedQuarticPairValue ε β (d.restrictComponent B.2) (orders B)
        (d.componentTimeAssignment shuffle τ B) a b := by
  unfold orderedQuarticPairValue
  rw [orderedQuarticLegOperator_componentOrderedLeg,
    orderedQuarticLegOperator_componentOrderedLeg]

end Fermionic

end Fermionic
end SecondQuantization
