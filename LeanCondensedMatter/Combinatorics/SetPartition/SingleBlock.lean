import Mathlib.Order.Partition.Finpartition

set_option linter.style.header false

/-!
# Single-block finite partitions

A finite partition with exactly one part consists of its entire support. This
elementary cardinality criterion is independent of replica weights or graph
connectivity.
-/

namespace Finpartition

variable {α : Type*} [DecidableEq α] {S : Finset α}

/-- A finite partition with one block has the whole support as that block. -/
theorem parts_eq_singleton_of_card_eq_one (π : Finpartition S)
    (h : π.parts.card = 1) : π.parts = {S} := by
  obtain ⟨B, hparts⟩ := Finset.card_eq_one.mp h
  have hBS : B = S := by
    simpa [hparts] using π.sup_parts
  simpa [hBS] using hparts

end Finpartition
