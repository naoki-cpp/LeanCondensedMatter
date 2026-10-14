import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.SlotSplit.SupportStandardization
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Pairing.MixedOrder

set_option linter.style.header false

/-!
# Mixed-order pairing in canonical external-support coordinates

Canonical increasing enumeration of a support finset preserves the flattened
external-first leg positions. The mixed-order pairing of its standalone
relabeling is therefore the original pairing transported only through the
standalone mixed-time permutation, without an additional slot shuffle.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

/-- The canonical external-support reindexing carries exactly the standalone
mixed-time pairing; the original gap positions of the support contribute no
extra pairing transport. No vacuum-free condition is required. -/
theorem ExternalInsertionDiagram.supportSlotCongr_pairingInMixedOrder
    {ExternalLabel InternalLabel : Type*} {E N : ℕ}
    (T : Finset (Fin N))
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N T)
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin N → ℝ) :
    let e : ↥T ≃ ↥(Finset.univ : Finset (Fin T.card)) :=
      (T.orderIsoOfFin rfl).toEquiv.symm.trans
        (Equiv.subtypeUnivEquiv
          (fun i : Fin T.card => Finset.mem_univ i)).symm
    let σT : Fin T.card → ℝ :=
      σ ∘ fun i => (T.orderIsoOfFin rfl i).1
    (d.slotCongr e).pairingInMixedOrder externalTime σT =
      d.pairing.transport
        (externalInsertionStandardToMixedAtomicPositionEquiv externalTime σT).symm := by
  intro e σT
  change (d.pairing.transport (externalInsertionLegCongr (E := E) e).symm).transport
    (externalInsertionMixedTimeAmbientPositionEquiv externalTime σT) =
      d.pairing.transport
        (externalInsertionStandardToMixedAtomicPositionEquiv externalTime σT).symm
  rw [PairingOn.transport_trans]
  have hleg := externalInsertionLegCongr_standardize (E := E) T
  change externalInsertionLegCongr (E := E) e =
    (finCongr (by simp) :
      Fin (2 * (2 * T.card + E)) ≃
        Fin (2 * (2 * (Finset.univ : Finset (Fin T.card)).card + E))) at hleg
  rw [hleg]
  congr 1

end Common
end SecondQuantization
