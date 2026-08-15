import LeanCondensedMatter.Combinatorics.BinaryShuffleSlotComplement
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.SlotSplitVacuumPairing

set_option linter.style.header false

/-!
# Slot-shuffle coordinates for two-point diagram fibers

Generic complement-cardinality and increasing-enumeration facts for binary slot shuffles are owned
by `Combinatorics/BinaryShuffleSlotComplement`. This module keeps only the diagram-specific bridge
to the inherited vacuum-slot map of a canonical two-point slot split.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

/-- The inherited vacuum-slot map of a canonical slot split is the right slot map of the shuffle,
after the unique cardinality cast from the complement to `Fin k`. -/
theorem slotSplitVacuumSlot_leftSlots_eq_slotShuffleRight
    {m k : ℕ} (shuffle : BinaryShuffle.SlotShuffle m k) (j : Fin k) :
    slotSplitVacuumSlot shuffle.leftSlots
        (Fin.cast shuffle.card_sdiff_leftSlots.symm j) =
      shuffle.slotEquiv (Sum.inr j) := by
  change
    ((Finset.univ : Finset (Fin (m + k))) \ shuffle.leftSlots).orderEmbOfFin rfl
        (Fin.cast shuffle.card_sdiff_leftSlots.symm j) =
      shuffle.slotEquiv (Sum.inr j)
  convert (shuffle.sdiffLeftSlots_orderEmbOfFin j) using 1
  apply Fin.ext
  rfl

end Common
end SecondQuantization
