import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Pairing.ComponentPairEquiv
import LeanCondensedMatter.Combinatorics.PerfectPairing.ComponentCrossing

set_option linter.style.header false

/-!
# Residual crossing parity of external-insertion components

For a generic external-insertion diagram, component-internal crossings need not account for the
entire global crossing parity. Distinct connected components can interleave in the canonical ambient
leg order, so their crossings contribute an explicit residual inter-component term.

This module identifies the residual parity with the component-leg block inversions.
Exact crossing-count decomposition follows directly from
`Combinatorics.Pairing.crossingCount_eq_sum_localCrossingCount_add_inter`; no
quartic-only parity cancellation is assumed.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*} {E N : ℕ}

/-- The residual inter-component crossing parity is the total block-inversion parity of the
canonical component-leg shuffle, relative to any explicit ordering of the connected components. -/
theorem ExternalInsertionDiagram.interComponentCrossingCount_mod_two_eq_orderedBlockInversionCount
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (blockOrder :
      d.vertexGraph.componentPartition.parts ≃ Fin (Fintype.card d.vertexGraph.componentPartition.parts)) :
    d.pairing.interComponentCrossingCount d.componentPairEquiv % 2 =
      d.componentLegShuffle.orderedBlockInversionCount blockOrder % 2 := by
  exact d.pairing.interComponentCrossingCount_mod_two_eq_orderedBlockInversionCount
    d.componentPairEquiv
    (fun B => (d.restrictComponent B).pairing.pairEndpointEquiv)
    d.componentLegShuffle
    (fun B p k => by
      fin_cases k <;>
        simp [ExternalInsertionDiagram.componentLegShuffle_slotEquiv_apply,
          Pairing.pairEndpointEquiv_apply, Pairing.pairEndpoint, pairEndpointAt,
          d.componentPairEquiv_apply])
    blockOrder

end Common
end SecondQuantization
