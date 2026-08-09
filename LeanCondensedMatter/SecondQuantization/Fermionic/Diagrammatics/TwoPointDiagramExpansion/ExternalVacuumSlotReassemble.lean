import LeanCondensedMatter.Combinatorics.BinaryShuffleSlotEquiv
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ExternalVacuumReassembleLaws
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.OrderedConnectivity
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.InteractionVertexRelabelConnected
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.OrderedAmplitude

set_option linter.style.header false

/-!
# Reassembling external and vacuum diagrams along a binary slot shuffle

For fixed local external and vacuum interaction slots, a binary slot shuffle selects the ambient
interaction vertices occupied by the connected external core. The local diagrams are transported to
those two complementary subsets and reassembled by the existing Common external/vacuum constructor.
This is the structural presentation used by the one finite diagram-sum reindex in the external-leg
linked-cluster theorem.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Combinatorics.BinaryShuffle

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- Arbitrary-set fixed-external diagrams whose complete graph is externally connected. -/
abbrev ExternallyConnectedFixedExternalTwoPointWickDiagramOn
    (Mode : Type*) (N : ℕ) (S : Finset (Fin N)) (i j : Mode) :=
  {d : FixedExternalTwoPointWickDiagramOn Mode N S i j // d.1.IsExternallyConnected}

noncomputable instance externallyConnectedFixedExternalTwoPointWickDiagramOnFintype
    (Mode : Type*) [Fintype Mode] (N : ℕ) (S : Finset (Fin N)) (i j : Mode) :
    Fintype (ExternallyConnectedFixedExternalTwoPointWickDiagramOn Mode N S i j) :=
  Fintype.ofFinite _

omit [LinearOrder Mode] [Fintype Mode] in
/-- The explicit diagram produced by the fixed-order equivalence is exactly the Common ordered
reindexing of the underlying arbitrary-set diagram. -/
theorem fixedExternalTwoPointWickDiagramOrderEquiv_val_eq_inInteractionOrder
    {N : ℕ} {S : Finset (Fin N)} (i j : Mode) (order : Common.QuarticVertexOrder S)
    (d : FixedExternalTwoPointWickDiagramOn Mode N S i j) :
    (fixedExternalTwoPointWickDiagramOrderEquiv i j order d).1 =
      d.1.inInteractionOrder order := by
  apply Common.TwoPointDiagram.ext
  · exact d.2.symm
  · funext v
    rfl
  · apply Combinatorics.Pairing.ext
    apply Equiv.ext
    intro leg
    apply Fin.ext
    rfl

omit [LinearOrder Mode] [Fintype Mode] in
/-- External connectedness is preserved by the fixed-order diagram equivalence. -/
theorem fixedExternalTwoPointWickDiagramOrderEquiv_isExternallyConnected_iff
    {N : ℕ} {S : Finset (Fin N)} (i j : Mode) (order : Common.QuarticVertexOrder S)
    (d : FixedExternalTwoPointWickDiagramOn Mode N S i j) :
    (fixedExternalTwoPointWickDiagramOrderEquiv i j order d).1.IsExternallyConnected ↔
      d.1.IsExternallyConnected := by
  rw [fixedExternalTwoPointWickDiagramOrderEquiv_val_eq_inInteractionOrder]
  exact d.1.inInteractionOrder_isExternallyConnected_iff order

/-- Restrict the fixed-order diagram equivalence to externally connected diagrams. -/
noncomputable def externallyConnectedFixedExternalTwoPointWickDiagramOrderEquiv
    {N : ℕ} {S : Finset (Fin N)} (i j : Mode) (order : Common.QuarticVertexOrder S) :
    ExternallyConnectedFixedExternalTwoPointWickDiagramOn Mode N S i j ≃
      ExternallyConnectedFixedExternalTwoPointWickDiagram Mode S.card i j :=
  (fixedExternalTwoPointWickDiagramOrderEquiv i j order).subtypeEquiv fun d =>
    (fixedExternalTwoPointWickDiagramOrderEquiv_isExternallyConnected_iff i j order d).symm

/-- Increasing order on the ambient slots occupied by the left side of a binary shuffle. -/
noncomputable def slotShuffleLeftVertexOrder {k m : ℕ} (shuffle : SlotShuffle k m) :
    Common.QuarticVertexOrder shuffle.leftSlots :=
  (finCongr shuffle.card_leftSlots).trans shuffle.leftSlotEquiv

/-- Increasing order on the ambient complement occupied by the right side of a binary shuffle. -/
noncomputable def slotShuffleRightComplementVertexOrder {k m : ℕ}
    (shuffle : SlotShuffle k m) :
    Common.QuarticVertexOrder
      ((Finset.univ : Finset (Fin (k + m))) \ shuffle.leftSlots) := by
  have h := Fintype.card_congr shuffle.rightComplementEquiv
  have hcard :
      ((Finset.univ : Finset (Fin (k + m))) \ shuffle.leftSlots).card = m := by
    simpa only [Fintype.card_coe, Fintype.card_fin] using h.symm
  exact (finCongr hcard).trans shuffle.rightComplementEquiv

/-- Reindex a quartic Wick diagram on an arbitrary finite vertex set to explicit `Fin |S|` slots. -/
noncomputable def quarticWickDiagramOrderEquiv {N : ℕ} {S : Finset (Fin N)}
    (order : Common.QuarticVertexOrder S) :
    QuarticWickDiagram Mode N S ≃
      QuarticWickDiagram Mode S.card (Finset.univ : Finset (Fin S.card)) := by
  let U : Finset (Fin S.card) := Finset.univ
  let hcard : U.card = S.card := by simp [U]
  let explicitOrder : Common.QuarticVertexOrder U :=
    (finCongr hcard).trans (Common.finEquivUnivSubtype S.card)
  exact (Common.quarticDiagramEquivOrderedData order).trans
    ((Equiv.cast
      (congrArg (Common.OrderedQuarticDiagramData (QuarticVertexLabel Mode)) hcard).symm).trans
      (Common.quarticDiagramEquivOrderedData explicitOrder).symm)

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
    i j (slotShuffleLeftVertexOrder shuffle)).symm externalCast

/-- Transport an explicit vacuum Wick diagram to the right-slot complement of a shuffle. -/
noncomputable def vacuumOnSlotShuffle {k m : ℕ}
    (vacuum : QuarticWickDiagram Mode m (Finset.univ : Finset (Fin m)))
    (shuffle : SlotShuffle k m) :
    QuarticWickDiagram Mode (k + m)
      ((Finset.univ : Finset (Fin (k + m))) \ shuffle.leftSlots) :=
  let order := slotShuffleRightComplementVertexOrder shuffle
  let h := Fintype.card_congr shuffle.rightComplementEquiv
  let hcard :
      ((Finset.univ : Finset (Fin (k + m))) \ shuffle.leftSlots).card = m := by
    simpa only [Fintype.card_coe, Fintype.card_fin] using h.symm
  let vacuumCast :
      QuarticWickDiagram Mode
        ((Finset.univ : Finset (Fin (k + m))) \ shuffle.leftSlots).card
        (Finset.univ : Finset
          (Fin ((Finset.univ : Finset (Fin (k + m))) \ shuffle.leftSlots).card)) :=
    Equiv.cast
      (congrArg
        (fun n => QuarticWickDiagram Mode n (Finset.univ : Finset (Fin n)))
        hcard.symm) vacuum
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

omit [LinearOrder Mode] [Fintype Mode] in
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
