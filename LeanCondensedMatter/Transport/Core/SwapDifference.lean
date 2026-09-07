import Mathlib.Algebra.Group.Basic

set_option linter.style.header false

/-!
# Raw swap differences

This module owns the raw difference obtained by exchanging two argument positions. It deliberately
does not include the factor `1/2` used for the antisymmetric part of a tensor.
-/

namespace QuantumTheory
namespace Transport

/-- Raw difference under exchange of two arguments: `f i j - f j i`. -/
def swapDifference {ι α : Type*} [AddGroup α]
    (f : ι → ι → α) (i j : ι) : α :=
  f i j - f j i

/-- Exchanging the two arguments reverses a raw swap difference. -/
theorem swapDifference_swap {ι α : Type*} [AddGroup α]
    (f : ι → ι → α) (i j : ι) :
    swapDifference f j i = -swapDifference f i j := by
  simp [swapDifference]

/-- A raw swap difference vanishes on equal arguments. -/
@[simp]
theorem swapDifference_self {ι α : Type*} [AddGroup α]
    (f : ι → ι → α) (i : ι) :
    swapDifference f i i = 0 := by
  simp [swapDifference]

end Transport
end QuantumTheory
