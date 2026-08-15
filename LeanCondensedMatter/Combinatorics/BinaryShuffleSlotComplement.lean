import LeanCondensedMatter.Combinatorics.BinaryShuffleSlotEquiv

set_option linter.style.header false

/-!
# Complement slots of ambient binary shuffles

This file records the generic complement-cardinality fact used when a binary slot shuffle splits
ambient slots into left and right families.
-/

namespace Combinatorics
namespace BinaryShuffle

/-- The complement of the left slots has the right perturbation order. -/
@[simp]
theorem SlotShuffle.card_sdiff_leftSlots {m n : ℕ} (shuffle : SlotShuffle m n) :
    ((Finset.univ : Finset (Fin (m + n))) \ shuffle.leftSlots).card = n := by
  have hright :
      (Finset.univ : Finset (Fin (m + n))) \ shuffle.leftSlots = shuffle.rightSlots := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    exact (shuffle.mem_rightSlots_iff_not_mem_leftSlots x).symm
  rw [hright, shuffle.card_rightSlots]

end BinaryShuffle
end Combinatorics
