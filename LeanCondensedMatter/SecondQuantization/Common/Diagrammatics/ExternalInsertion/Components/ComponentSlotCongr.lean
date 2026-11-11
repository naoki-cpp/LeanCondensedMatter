import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Components.MixedOrderData
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.SlotSplit.SupportStandardization

set_option linter.style.header false

/-!
# Canonical reindexing of external-insertion connected components

The connected-component restriction retains the original interaction-vertex
subset. Its standalone ordered diagram enumerates the interaction slots
in increasing order. We identify that operation with the already defined
`slotCongr` transport, including the *actual pairing*, not just labels.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*}

/-- The consecutive interaction-slot component diagram is exactly the
canonical `slotCongr` relabeling of its actual connected-component
restriction. This retains its external labels, interaction labels and
flattened-leg Wick pairing. -/
theorem ExternalInsertionDiagram.componentOrderedDiagram_eq_slotCongr
    {E n : ℕ}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E n
      (Finset.univ : Finset (Fin n)))
    (B : d.vertexGraph.componentPartition.parts) :
    let T := interactionSector
      (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))
    d.componentOrderedDiagram B =
      (d.restrictComponent B).slotCongr (standardSlotEquiv T) := by
  classical
  dsimp only
  let T := interactionSector
    (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))
  let r := d.restrictComponent B
  apply ExternalInsertionDiagram.ext
  · rfl
  · funext v
    change r.vertexLabel (T.orderIsoOfFin rfl v.1) =
      r.vertexLabel ((standardSlotEquiv T).symm v)
    congr 1
  · change (Equiv.cast (show Pairing (2 * T.card + d.externalPairCount B) =
          PairingOn (Fin (2 * (2 * (Finset.univ : Finset (Fin T.card)).card +
            d.externalPairCount B))) from by simp [Pairing]) r.pairing) =
        r.pairing.transport
          (externalInsertionLegCongr (E := d.externalPairCount B)
            (standardSlotEquiv T)).symm
    rw [externalInsertionLegCongr_standardize (E := d.externalPairCount B) T]
    apply PairingOn.ext
    apply Equiv.ext
    intro p
    simp only [PairingOn.transport_partner]
    have hcard : 2 * T.card + d.externalPairCount B =
        2 * (Finset.univ : Finset (Fin T.card)).card +
          d.externalPairCount B := by
      simp
    have hback := Pairing.cast_partner hcard r.pairing p
    have hforward :=
      congrArg (finCongr (congrArg (fun k : ℕ => 2 * k) hcard)) hback
    have hsymm :
        finCongr (congrArg (fun k : ℕ => 2 * k) hcard.symm) =
          (finCongr (congrArg (fun k : ℕ => 2 * k) hcard)).symm := by
      apply Equiv.ext
      intro x
      apply Fin.ext
      rfl
    rw [hsymm] at hforward
    simpa only [Equiv.symm_symm, Equiv.apply_symm_apply] using hforward

end Common
end SecondQuantization
