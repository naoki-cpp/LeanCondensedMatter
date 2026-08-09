import LeanCondensedMatter.Combinatorics.BinaryShuffleSlotEquiv
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ExternalVacuumReassembleLaws
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Ordered
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.AmplitudeFactorization

set_option linter.style.header false

/-!
# Reassembling external and vacuum diagrams along a binary slot shuffle

For fixed local external and vacuum interaction slots, a binary slot shuffle selects the ambient
interaction vertices occupied by the connected external core.  The local diagrams are transported to
those two complementary subsets and reassembled by the existing Common external/vacuum constructor.
This is the structural presentation used by the one finite diagram-sum reindex in the external-leg
linked-cluster theorem.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Combinatorics.BinaryShuffle

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- Increasing order on the ambient slots occupied by the left side of a binary shuffle. -/
noncomputable def SlotShuffle.leftVertexOrder {k m : ℕ} (shuffle : SlotShuffle k m) :
    Common.QuarticVertexOrder shuffle.leftSlots :=
  (finCongr shuffle.card_leftSlots).trans shuffle.leftSlotEquiv

/-- Increasing order on the ambient complement occupied by the right side of a binary shuffle. -/
noncomputable def SlotShuffle.rightComplementVertexOrder {k m : ℕ}
    (shuffle : SlotShuffle k m) :
    Common.QuarticVertexOrder
      ((Finset.univ : Finset (Fin (k + m))) \ shuffle.leftSlots) := by
  have hcard :
      ((Finset.univ : Finset (Fin (k + m))) \ shuffle.leftSlots).card = m := by
    have h := Fintype.card_congr shuffle.rightComplementEquiv
    simpa using h.symm
  exact (finCongr hcard).trans shuffle.rightComplementEquiv

/-- Reindex a quartic Wick diagram on an arbitrary finite vertex set to explicit `Fin |S|` slots. -/
noncomputable def quarticWickDiagramOrderEquiv {N : ℕ} {S : Finset (Fin N)}
    (order : Common.QuarticVertexOrder S) :
    QuarticWickDiagram Mode N S ≃
      QuarticWickDiagram Mode S.card (Finset.univ : Finset (Fin S.card)) :=
  (Common.quarticDiagramEquivOrderedData order).trans
    (Common.quarticDiagramEquivOrderedData (Common.finEquivUnivSubtype S.card)).symm

/-- Transport an explicit connected external diagram to the left-slot subset of a shuffle. -/
noncomputable def connectedExternalOnSlotShuffle {k m : ℕ} (i j : Mode)
    (external : ExternallyConnectedFixedExternalTwoPointWickDiagram Mode k i j)
    (shuffle : SlotShuffle k m) :
    ExternallyConnectedFixedExternalTwoPointWickDiagramOn
      Mode (k + m) shuffle.leftSlots i j :=
  let externalCast :
      ExternallyConnectedFixedExternalTwoPointWickDiagram
        Mode shuffle.leftSlots.card i j :=
    Equiv.cast
      (congrArg (fun n => ExternallyConnectedFixedExternalTwoPointWickDiagram Mode n i j)
        shuffle.card_leftSlots.symm) external
  (externallyConnectedFixedExternalTwoPointWickDiagramOrderEquiv
    i j shuffle.leftVertexOrder).symm externalCast

/-- Transport an explicit vacuum Wick diagram to the right-slot complement of a shuffle. -/
noncomputable def vacuumOnSlotShuffle {k m : ℕ}
    (vacuum : QuarticWickDiagram Mode m (Finset.univ : Finset (Fin m)))
    (shuffle : SlotShuffle k m) :
    QuarticWickDiagram Mode (k + m)
      ((Finset.univ : Finset (Fin (k + m))) \ shuffle.leftSlots) :=
  let order := shuffle.rightComplementVertexOrder
  let vacuumCast :
      QuarticWickDiagram Mode
        ((Finset.univ : Finset (Fin (k + m))) \ shuffle.leftSlots).card
        (Finset.univ : Finset
          (Fin ((Finset.univ : Finset (Fin (k + m))) \ shuffle.leftSlots).card)) :=
    Equiv.cast
      (congrArg
        (fun n => QuarticWickDiagram Mode n (Finset.univ : Finset (Fin n)))
        (by
          have h := Fintype.card_congr shuffle.rightComplementEquiv
          simpa using h)) vacuum
  (quarticWickDiagramOrderEquiv (Mode := Mode) order).symm vacuumCast

/-- Reassemble one connected external diagram and one vacuum diagram according to a binary slot
shuffle. -/
noncomputable def reassembleExternalVacuumSlotShuffle {k m : ℕ} (i j : Mode)
    (external : ExternallyConnectedFixedExternalTwoPointWickDiagram Mode k i j)
    (vacuum : QuarticWickDiagram Mode m (Finset.univ : Finset (Fin m)))
    (shuffle : SlotShuffle k m) :
    FixedExternalTwoPointWickDiagram Mode (k + m) i j := by
  let externalOn := connectedExternalOnSlotShuffle i j external shuffle
  let vacuumOn := vacuumOnSlotShuffle vacuum shuffle
  refine ⟨Common.TwoPointDiagram.reassembleExternalVacuum
      (Finset.subset_univ shuffle.leftSlots) ⟨externalOn.1.1, externalOn.2⟩ vacuumOn, ?_⟩
  simpa [Common.TwoPointDiagram.reassembleExternalVacuum] using externalOn.1.2

/-- The reassembled diagram has exactly the shuffle's left slots in its external component. -/
theorem reassembleExternalVacuumSlotShuffle_externalInteractionPart {k m : ℕ} (i j : Mode)
    (external : ExternallyConnectedFixedExternalTwoPointWickDiagram Mode k i j)
    (vacuum : QuarticWickDiagram Mode m (Finset.univ : Finset (Fin m)))
    (shuffle : SlotShuffle k m) :
    Common.TwoPointDiagram.interactionPart
      ((reassembleExternalVacuumSlotShuffle i j external vacuum shuffle).1.externalComponent 0) =
      shuffle.leftSlots := by
  let externalOn := connectedExternalOnSlotShuffle i j external shuffle
  let vacuumOn := vacuumOnSlotShuffle vacuum shuffle
  change Common.TwoPointDiagram.interactionPart
      ((Common.TwoPointDiagram.reassembleExternalVacuum
        (Finset.subset_univ shuffle.leftSlots) ⟨externalOn.1.1, externalOn.2⟩ vacuumOn).externalComponent 0) =
    shuffle.leftSlots
  exact Common.TwoPointDiagram.interactionPart_externalComponent_reassembleExternalVacuum
    (Finset.subset_univ shuffle.leftSlots) ⟨externalOn.1.1, externalOn.2⟩ vacuumOn

end Fermionic
end SecondQuantization
