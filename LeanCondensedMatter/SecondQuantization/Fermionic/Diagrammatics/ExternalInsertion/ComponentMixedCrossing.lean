import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.Diagram
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Components.MixedOrderData
import LeanCondensedMatter.Combinatorics.PerfectPairing.ComponentCrossing

set_option linter.style.header false

/-!
# Mixed-order component crossing parity

The component-local mixed positions form an order-preserving family shuffle into the ambient
mixed-time atomic order. The generic perfect-pairing crossing-parity theorem identifies the residual
inter-component crossing count modulo two with the ordered block-inversion count of this shuffle.

This module provides the mixed-position shuffle and the crossing-parity bridge. Pairing-weight
factorization and fermionic time-order permutation-sign identities belong to downstream modules.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Common
open scoped BigOperators

variable {Mode : Type*}

/-- The canonical family shuffle from component-local mixed atomic positions to the ambient
mixed-time atomic positions. -/
noncomputable def ExternalInsertionWickDiagram.componentMixedPositionShuffle
    {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    FamilySlotShuffleTo
      (fun B : d.vertexGraph.componentPartition.parts =>
        2 * (2 * (interactionSector
          (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))).card +
            d.externalPairCount B))
      (2 * (2 * n + E)) where
  slotEquiv := d.componentMixedPositionEquiv externalTime σ
  strictMono := fun B => by
    intro a b hab
    simpa only [Common.ExternalInsertionDiagram.componentMixedPositionEquiv_apply] using
      d.componentMixedPosition_strictMono externalTime σ B hab

@[simp]
theorem ExternalInsertionWickDiagram.componentMixedPositionShuffle_slotEquiv_apply
    {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (B : d.vertexGraph.componentPartition.parts)
    (p : Fin (2 * (2 * (interactionSector
      (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))).card +
        d.externalPairCount B))) :
    (d.componentMixedPositionShuffle externalTime σ).slotEquiv ⟨B, p⟩ =
      d.componentMixedPosition externalTime σ B p :=
  d.componentMixedPositionEquiv_apply externalTime σ B p

/-- Total oriented crossing count between distinct connected components in ambient mixed order. -/
noncomputable def ExternalInsertionWickDiagram.mixedInterComponentCrossingCount
    {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) : ℕ :=
  (d.pairingInMixedOrder externalTime σ).interComponentCrossingCount
    (d.componentMixedPairEquiv externalTime σ)

/-- The residual mixed-order inter-component crossing parity is the total inversion parity of the
canonical mixed component-position shuffle. -/
theorem ExternalInsertionWickDiagram.mixedInterComponentCrossingCount_mod_two_eq_orderedBlockInversionCount
    {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
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
        simp [ExternalInsertionWickDiagram.componentMixedPositionShuffle_slotEquiv_apply,
          Pairing.pairEndpointEquiv_apply, Pairing.pairEndpoint, pairEndpointAt,
          d.componentMixedPairEquiv_apply externalTime σ])
    blockOrder

end Fermionic
end SecondQuantization
