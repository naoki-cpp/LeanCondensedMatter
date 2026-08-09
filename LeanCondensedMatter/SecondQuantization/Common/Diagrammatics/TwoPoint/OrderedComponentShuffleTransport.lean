import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.OrderedComponentTransport

set_option linter.style.header false

/-!
# Two-point component shuffles under interaction ordering

The graph isomorphism induced by an interaction-vertex order transports both the component index and
the number of interaction vertices in every component.  Reindexing the generic finite family shuffle
along this component equivalence therefore identifies the component-shuffle types before and after
ordering.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*} {N : ℕ}

noncomputable section

/-- Component interaction shuffles of an explicit ordered diagram are canonically the component
interaction shuffles of the original ambient diagram. -/
def TwoPointDiagram.inInteractionOrderComponentShuffleEquiv
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (order : QuarticVertexOrder S) :
    (d.inInteractionOrder order).ComponentInteractionShuffle ≃
      d.ComponentInteractionShuffle := by
  let dOrdered := d.inInteractionOrder order
  let ePart := d.inInteractionOrderComponentPartEquiv order
  have hsize : dOrdered.interactionComponentSize =
      fun B => d.interactionComponentSize (ePart B) := by
    funext B
    exact d.interactionComponentSize_inInteractionOrder_eq order B
  let hfamily : FamilySlotShuffle dOrdered.interactionComponentSize ≃
      FamilySlotShuffle (fun B => d.interactionComponentSize (ePart B)) :=
    Equiv.cast (congrArg FamilySlotShuffle hsize)
  exact dOrdered.componentInteractionFamilyShuffleEquiv.symm |>.trans <|
    hfamily.trans <|
      (FamilySlotShuffle.reindexEquiv ePart d.interactionComponentSize).symm |>.trans
        d.componentInteractionFamilyShuffleEquiv

end

end Common
end SecondQuantization
