import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Components.MixedOrderData
import LeanCondensedMatter.Combinatorics.PerfectPairing.ComponentCrossing
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.PairingWeight

set_option linter.style.header false

/-!
# Mixed-order component crossings and exchange weights

Component mixed positions form an order-preserving family shuffle into ambient mixed order.
Crossing counts and their parity decompose through the component pairing equivalence; exchange
weights factor for either statistics. Labels are arbitrary and no thermal kernel is used.
-/

namespace SecondQuantization
namespace Common

open Combinatorics
open scoped BigOperators

variable {ExternalLabel InternalLabel : Type*}

/-- Total oriented crossing count between distinct connected components in ambient mixed order. -/
noncomputable def ExternalInsertionDiagram.mixedInterComponentCrossingCount
    {E n : ℕ}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E n
      (Finset.univ : Finset (Fin n)))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) : ℕ :=
  (d.pairingInMixedOrder externalTime σ).interComponentCrossingCount
    (d.componentMixedPairEquiv externalTime σ)

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
    d.mixedInterComponentCrossingCount externalTime σ % 2 =
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

/-- The mixed-order crossing count is the sum of component-local mixed crossing counts and
the residual crossings between distinct components. -/
theorem ExternalInsertionDiagram.pairingInMixedOrder_crossingCount_eq_sum_components_add_inter
    {E n : ℕ}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E n
      (Finset.univ : Finset (Fin n)))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    (d.pairingInMixedOrder externalTime σ).crossingCount =
      (∑ B : d.vertexGraph.componentPartition.parts,
        ((d.componentOrderedDiagram B).pairingInMixedOrder
          (d.componentExternalTime externalTime B)
          (d.componentInteractionTime σ B)).crossingCount) +
      (d.pairingInMixedOrder externalTime σ).interComponentCrossingCount
        (d.componentMixedPairEquiv externalTime σ) := by
  rw [Pairing.crossingCount_eq_sum_componentCrossingCount_diag_add_inter
    (d.pairingInMixedOrder externalTime σ)
    (d.componentMixedPairEquiv externalTime σ)]
  apply congrArg (fun k : ℕ =>
    k + (d.pairingInMixedOrder externalTime σ).interComponentCrossingCount
      (d.componentMixedPairEquiv externalTime σ))
  apply Finset.sum_congr rfl
  intro B _
  exact Pairing.componentCrossingCount_self_eq
    (d.pairingInMixedOrder externalTime σ)
    ((d.componentOrderedDiagram B).pairingInMixedOrder
      (d.componentExternalTime externalTime B)
      (d.componentInteractionTime σ B))
    (d.componentMixedPairEquiv externalTime σ) B
    (Equiv.refl _)
    (d.componentMixedPosition externalTime σ B)
    (d.componentMixedPosition_strictMono externalTime σ B)
    (fun pr => by
      simpa using d.componentMixedPairEquiv_apply externalTime σ B pr)

/-- The exchange-statistics weight of the mixed-order pairing factors into a residual
inter-component weight and the standalone mixed-order component weights. -/
theorem ExternalInsertionDiagram.pairingInMixedOrder_weight_eq_inter_mul_prod_components
    {E n : ℕ}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E n
      (Finset.univ : Finset (Fin n)))
    (s : Common.Statistics)
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    (d.pairingInMixedOrder externalTime σ).weight s =
      (s.zetaInt : ℂ) ^
        (d.pairingInMixedOrder externalTime σ).interComponentCrossingCount
          (d.componentMixedPairEquiv externalTime σ) *
      ∏ B : d.vertexGraph.componentPartition.parts,
        ((d.componentOrderedDiagram B).pairingInMixedOrder
          (d.componentExternalTime externalTime B)
          (d.componentInteractionTime σ B)).weight s := by
  simp only [Pairing.weight]
  rw [d.pairingInMixedOrder_crossingCount_eq_sum_components_add_inter externalTime σ,
    pow_add, ← Finset.prod_pow_eq_pow_sum]
  ac_rfl

end Common
end SecondQuantization
