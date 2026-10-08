import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Pairing.ComponentPairEquiv
import LeanCondensedMatter.Combinatorics.PerfectPairing.ComponentCrossing
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.PairingWeight

set_option linter.style.header false

/-!
# Crossing decomposition for external-insertion components

For a generic external-insertion diagram, component-internal crossings need not account for the
entire global crossing parity. Distinct connected components can interleave in the canonical ambient
leg order, so their crossings contribute an explicit residual inter-component term.

This module isolates that residual exactly. It does not assume the quartic-only parity cancellation.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*} {E N : ℕ}

/-- Total oriented crossing count between distinct connected components of an external-insertion
diagram. -/
noncomputable def ExternalInsertionDiagram.interComponentCrossingCount
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S) : ℕ :=
  d.pairing.interComponentCrossingCount d.componentPairEquiv


/-- The residual inter-component crossing parity is the total block-inversion parity of the
canonical component-leg shuffle, relative to any explicit ordering of the connected components. -/
theorem ExternalInsertionDiagram.interComponentCrossingCount_mod_two_eq_orderedBlockInversionCount
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (blockOrder :
      d.vertexGraph.componentPartition.parts ≃ Fin (Fintype.card d.vertexGraph.componentPartition.parts)) :
    d.interComponentCrossingCount % 2 =
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

/-- The ambient crossing count is the sum of all component-local crossing counts plus the residual
crossing count between distinct connected components. -/
theorem ExternalInsertionDiagram.crossingCount_eq_sum_components_add_inter
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S) :
    d.pairing.crossingCount =
      (∑ B : d.vertexGraph.componentPartition.parts, (d.restrictComponent B).pairing.crossingCount) +
        d.interComponentCrossingCount := by
  rw [d.pairing.crossingCount_eq_sum_componentCrossingCount_diag_add_inter d.componentPairEquiv]
  apply congrArg (fun n : ℕ => n + d.interComponentCrossingCount)
  apply Finset.sum_congr rfl
  intro B _
  exact Combinatorics.Pairing.componentCrossingCount_self_eq
    d.pairing (d.restrictComponent B).pairing d.componentPairEquiv B
    (Equiv.refl (d.restrictComponent B).pairing.NormalizedPair)
    (d.componentDiagramLeg B)
    (d.componentDiagramLegOrderEmbedding B).strictMono
    (fun pr => by simpa using d.componentPairEquiv_apply B pr)

/-- The exchange-statistics weight factors into the residual inter-component exchange sign and the
product of component-local pairing weights. -/
theorem ExternalInsertionDiagram.weight_eq_inter_mul_prod_components
    (s : Statistics) {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S) :
    d.pairing.weight s =
      (s.zetaInt : ℂ) ^ d.interComponentCrossingCount *
        ∏ B : d.vertexGraph.componentPartition.parts, (d.restrictComponent B).pairing.weight s := by
  classical
  simp only [Combinatorics.Pairing.weight]
  rw [d.crossingCount_eq_sum_components_add_inter, pow_add,
    ← Finset.prod_pow_eq_pow_sum]
  exact mul_comm _ _

end Common
end SecondQuantization
