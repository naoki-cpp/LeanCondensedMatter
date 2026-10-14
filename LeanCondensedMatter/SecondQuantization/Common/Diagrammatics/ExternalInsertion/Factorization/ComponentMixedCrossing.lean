import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Pairing.ComponentMixedPairEquiv
import LeanCondensedMatter.Combinatorics.PerfectPairing.ComponentCrossing

set_option linter.style.header false

/-!
# Mixed-order component crossings

Component mixed positions form an order-preserving family shuffle into ambient mixed order.
Residual crossing parity is related to ordered block inversions through the component pairing
equivalence. The exact crossing decomposition is supplied directly by the generic
`Pairing.crossingCount_eq_sum_localCrossingCount_add_inter`, while the statistics-generic
exchange-weight conversion belongs to `BlochDeDominicis.PairingWeight`.
Labels are arbitrary and no thermal kernel is used.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*}

/-- The residual mixed-order inter-component crossing parity is the total inversion parity of the
canonical mixed component-position shuffle. -/
theorem ExternalInsertionDiagram.mixedInterComponentCrossingCount_mod_two_eq_orderedBlockInversionCount
    {E n : ℕ}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E n
      (Finset.univ : Finset (Fin n)))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (blockOrder :
      d.vertexGraph.componentPartition.parts ≃
        Fin (Fintype.card d.vertexGraph.componentPartition.parts)) :
    (d.pairingInMixedOrder externalTime σ).interComponentCrossingCount
          (d.componentMixedPairEquiv externalTime σ) % 2 =
      (d.componentMixedPositionShuffle externalTime σ).orderedBlockInversionCount blockOrder % 2 := by
  exact Pairing.interComponentCrossingCount_mod_two_eq_orderedBlockInversionCount
    (d.pairingInMixedOrder externalTime σ)
    (d.componentMixedPairEquiv externalTime σ)
    (fun B =>
      ((d.componentOrderedDiagram B).pairingInMixedOrder
        (d.componentExternalTime externalTime B)
        (d.componentInteractionTime σ B)).pairEndpointEquiv)
    (d.componentMixedPositionShuffle externalTime σ)
    (fun B p k => by
      fin_cases k <;>
        simp [ExternalInsertionDiagram.componentMixedPositionShuffle_slotEquiv_apply,
          Pairing.pairEndpointEquiv_apply, Pairing.pairEndpoint, pairEndpointAt,
          d.componentMixedPairEquiv_apply externalTime σ])
    blockOrder

end Common
end SecondQuantization
