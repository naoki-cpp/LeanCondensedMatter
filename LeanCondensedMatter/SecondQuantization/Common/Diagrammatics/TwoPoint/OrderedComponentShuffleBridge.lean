import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.CanonicalComponentShuffle
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.OrderedComponentShuffleTransport

set_option linter.style.header false

/-!
# Canonical component shuffle under interaction ordering

The canonical component shuffle of an explicitly ordered two-point diagram, transported back to the
ambient diagram, is exactly the shuffle induced by that global interaction order and its induced
component-local orders. This is the Common-layer bridge used by the external-leg linked-cluster
finite order reindexing.
-/

namespace SecondQuantization
namespace Common

variable {ExternalLabel InternalLabel : Type*} {N : ℕ}

noncomputable section

/-- Transporting the canonical component shuffle of an ordered presentation back to the ambient
diagram recovers the component shuffle read off from that global interaction order. -/
theorem TwoPointDiagram.inInteractionOrderComponentShuffleEquiv_canonical
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (order : QuarticVertexOrder S) :
    d.inInteractionOrderComponentShuffleEquiv order
        (d.inInteractionOrder order).canonicalComponentInteractionShuffle =
      d.interactionShuffleOfVertexOrder order
        (d.componentInteractionVertexOrdersOfVertexOrder order)
        (d.componentInteractionOrdersCompatible_ofVertexOrder order) := by
  apply Combinatorics.FamilySlotShuffleTo.ext
  apply Equiv.ext
  rintro ⟨B, i⟩
  simp [TwoPointDiagram.inInteractionOrderComponentShuffleEquiv,
    TwoPointDiagram.componentInteractionFamilyShuffleEquiv,
    Combinatorics.FamilySlotShuffle.reindexEquiv,
    Combinatorics.FamilySlotShuffleTo.castTotalEquiv,
    TwoPointDiagram.interactionShuffleOfVertexOrder,
    TwoPointDiagram.componentInteractionVertexEquiv,
    TwoPointDiagram.componentInteractionVertexOrdersOfVertexOrder,
    TwoPointDiagram.componentInteractionVertexOrderOfVertexOrder,
    TwoPointDiagram.canonicalComponentInteractionShuffle]

end

end Common
end SecondQuantization
