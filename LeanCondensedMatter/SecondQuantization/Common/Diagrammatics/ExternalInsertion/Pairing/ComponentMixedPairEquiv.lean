import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Components.MixedOrderData
import LeanCondensedMatter.Combinatorics.PerfectPairing.ComponentDecomposition

set_option linter.style.header false

/-!
# Mixed-order normalized-pair decomposition of external-insertion components

The canonical component mixed-position equivalence intertwines ambient and component partner
maps. The generic perfect-pairing decomposition then identifies local normalized pairs with
ambient mixed-order normalized pairs, preserving the ordered endpoints. Mixed-time position and
shuffle data belong to the upstream component-data layer.
-/

namespace SecondQuantization
namespace Common

variable {ExternalLabel InternalLabel : Type*}

/-- Component-local mixed-order normalized pairs, over all connected components, are equivalent to
the ambient mixed-order normalized pairs. The position equivalence is only the fixed component
shuffle transported through mixed/fixed position equivalences. -/
noncomputable def ExternalInsertionDiagram.componentMixedPairEquiv
    {E n : ℕ}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E n
      (Finset.univ : Finset (Fin n)))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    (Σ B : d.vertexGraph.componentPartition.parts,
      ((d.componentOrderedDiagram B).pairingInMixedOrder
        (d.componentExternalTime externalTime B)
        (d.componentInteractionTime σ B)).NormalizedPair) ≃
      (d.pairingInMixedOrder externalTime σ).NormalizedPair :=
  (d.pairingInMixedOrder externalTime σ).normalizedPairSigmaEquiv
    (fun B =>
      (d.componentOrderedDiagram B).pairingInMixedOrder
        (d.componentExternalTime externalTime B)
        (d.componentInteractionTime σ B))
    (d.componentMixedPositionEquiv externalTime σ)
    (fun B p => by
      simpa only [ExternalInsertionDiagram.componentMixedPositionEquiv_apply] using
        d.pairingInMixedOrder_partner_componentMixedPosition externalTime σ B p)

/-- The all-component mixed pair equivalence maps a local normalized pair by applying
`componentMixedPosition` to its two endpoints. -/
@[simp]
theorem ExternalInsertionDiagram.componentMixedPairEquiv_apply
    {E n : ℕ}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E n
      (Finset.univ : Finset (Fin n)))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (B : d.vertexGraph.componentPartition.parts)
    (pr : ((d.componentOrderedDiagram B).pairingInMixedOrder
      (d.componentExternalTime externalTime B)
      (d.componentInteractionTime σ B)).NormalizedPair) :
    (d.componentMixedPairEquiv externalTime σ ⟨B, pr⟩).1 =
      (d.componentMixedPosition externalTime σ B pr.1.1,
        d.componentMixedPosition externalTime σ B pr.1.2) := by
  let componentPairing := fun C : d.vertexGraph.componentPartition.parts =>
    (d.componentOrderedDiagram C).pairingInMixedOrder
      (d.componentExternalTime externalTime C)
      (d.componentInteractionTime σ C)
  let hpartner : ∀ C p,
      (d.pairingInMixedOrder externalTime σ).partner
          (d.componentMixedPositionEquiv externalTime σ ⟨C, p⟩) =
        d.componentMixedPositionEquiv externalTime σ
          ⟨C, (componentPairing C).partner p⟩ := by
    intro C p
    simpa only [ExternalInsertionDiagram.componentMixedPositionEquiv_apply] using
      d.pairingInMixedOrder_partner_componentMixedPosition externalTime σ C p
  simpa only [ExternalInsertionDiagram.componentMixedPairEquiv,
    ExternalInsertionDiagram.componentMixedPositionEquiv_apply] using
    (Combinatorics.Pairing.normalizedPairSigmaEquiv_apply_of_strictMono
      (d.pairingInMixedOrder externalTime σ)
      componentPairing
      (d.componentMixedPositionEquiv externalTime σ)
      hpartner
      (fun C => by
        simpa only [ExternalInsertionDiagram.componentMixedPositionEquiv_apply] using
          d.componentMixedPosition_strictMono externalTime σ C)
      B pr)

end Common
end SecondQuantization
