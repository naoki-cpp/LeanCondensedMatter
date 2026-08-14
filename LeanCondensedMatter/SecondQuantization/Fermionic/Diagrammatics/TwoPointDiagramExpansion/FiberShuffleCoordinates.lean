import LeanCondensedMatter.Combinatorics.BinaryShuffleSlotEquiv
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.SlotSplitVacuumPairing

set_option linter.style.header false

/-!
# Coordinates of a fixed external-slot fiber under a binary slot shuffle

The coefficientwise Cauchy-product proof groups external-slot fibers by the number of slots in the
external component.  A `SlotShuffle m k` then records which of the `m + k` ambient interaction slots
belong to that component.  The analytic shuffle theorem uses the shuffle's left/right slot maps,
while the canonical fiber uses increasing `Finset` enumerations of the external set and its
complement.

This module identifies those coordinate maps.  The statements are deliberately tied to the
canonical fiber route: no second diagram decomposition or mixed-position factorization is
introduced.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Common

/-- The canonical increasing enumeration of a shuffle's left-slot set is its left slot map. -/
theorem slotShuffleLeftSlots_orderEmbOfFin {m k : ℕ}
    (shuffle : BinaryShuffle.SlotShuffle m k) (i : Fin m) :
    shuffle.leftSlots.orderEmbOfFin shuffle.card_leftSlots i =
      shuffle.slotEquiv (Sum.inl i) := by
  have h := Finset.orderEmbOfFin_unique
    (s := shuffle.leftSlots) (h := shuffle.card_leftSlots)
    (f := fun q => shuffle.slotEquiv (Sum.inl q))
    (fun q => (shuffle.mem_leftSlots_iff _).2 ⟨q, rfl⟩)
    shuffle.strictMonoLeft
  exact congrFun h.symm i

/-- The complement of the left slots is exactly the right-slot set. -/
theorem slotShuffle_sdiff_leftSlots_eq_rightSlots {m k : ℕ}
    (shuffle : BinaryShuffle.SlotShuffle m k) :
    (Finset.univ : Finset (Fin (m + k))) \ shuffle.leftSlots = shuffle.rightSlots := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
  exact (shuffle.mem_rightSlots_iff_not_mem_leftSlots x).symm

/-- Hence the complement of the left slots has the right perturbation order. -/
@[simp]
theorem slotShuffle_card_sdiff_leftSlots {m k : ℕ}
    (shuffle : BinaryShuffle.SlotShuffle m k) :
    ((Finset.univ : Finset (Fin (m + k))) \ shuffle.leftSlots).card = k := by
  rw [slotShuffle_sdiff_leftSlots_eq_rightSlots, shuffle.card_rightSlots]

/-- The canonical increasing enumeration of the complement is the shuffle's right slot map. -/
theorem slotShuffleSdiffLeftSlots_orderEmbOfFin {m k : ℕ}
    (shuffle : BinaryShuffle.SlotShuffle m k) (j : Fin k) :
    ((Finset.univ : Finset (Fin (m + k))) \ shuffle.leftSlots).orderEmbOfFin
        (slotShuffle_card_sdiff_leftSlots shuffle) j =
      shuffle.slotEquiv (Sum.inr j) := by
  have h := Finset.orderEmbOfFin_unique
    (s := (Finset.univ : Finset (Fin (m + k))) \ shuffle.leftSlots)
    (h := slotShuffle_card_sdiff_leftSlots shuffle)
    (f := fun q => shuffle.slotEquiv (Sum.inr q))
    (fun q => by
      rw [slotShuffle_sdiff_leftSlots_eq_rightSlots]
      exact (shuffle.mem_rightSlots_iff _).2 ⟨q, rfl⟩)
    shuffle.strictMonoRight
  exact congrFun h.symm j

/-- The inherited vacuum-slot map of the canonical fiber is the right slot map of the shuffle,
after the unique cardinality cast from the complement to `Fin k`. -/
theorem slotSplitVacuumSlot_leftSlots_eq_slotShuffleRight
    {m k : ℕ} (shuffle : BinaryShuffle.SlotShuffle m k) (j : Fin k) :
    slotSplitVacuumSlot shuffle.leftSlots
        (Fin.cast (slotShuffle_card_sdiff_leftSlots shuffle).symm j) =
      shuffle.slotEquiv (Sum.inr j) := by
  change
    ((Finset.univ : Finset (Fin (m + k))) \ shuffle.leftSlots).orderEmbOfFin rfl
        (Fin.cast (slotShuffle_card_sdiff_leftSlots shuffle).symm j) =
      shuffle.slotEquiv (Sum.inr j)
  convert (slotShuffleSdiffLeftSlots_orderEmbOfFin shuffle j) using 1
  apply Fin.ext
  rfl

end Fermionic
end SecondQuantization
