import Mathlib.Algebra.Group.Basic

set_option linter.style.header false

/-!
# Raw swap differences

`swapDifference` is `f i j - f j i`; unlike an antisymmetric part, it has no factor `1/2`.
-/

namespace QuantumTheory.Transport

/-- Raw difference under exchange of two arguments. -/
def swapDifference {ι α : Type*} [AddGroup α]
    (f : ι → ι → α) (i j : ι) : α :=
  f i j - f j i

/-- Exchanging the two arguments reverses a raw swap difference. -/
theorem swapDifference_swap {ι α : Type*} [AddGroup α]
    (f : ι → ι → α) (i j : ι) :
    swapDifference f j i = -swapDifference f i j := by
  simp [swapDifference]

/-- A raw swap difference vanishes on equal arguments. -/
@[simp] theorem swapDifference_self {ι α : Type*} [AddGroup α]
    (f : ι → ι → α) (i : ι) :
    swapDifference f i i = 0 := by
  simp [swapDifference]

end QuantumTheory.Transport
