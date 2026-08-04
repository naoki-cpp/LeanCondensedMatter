import LeanCondensedMatter.QuantumTheory.DensityOperator.Basic

/-!
# Discrete POVMs

A discrete POVM is a countable family of positive bounded effects that sums strongly to the
identity.
-/

namespace QuantumTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A discrete POVM with countably many positive bounded effects summing strongly to the identity. -/
structure POVM (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (M : Type*) [Countable M] where
  /-- The bounded effect associated with each measurement outcome. -/
  E : M → H →L[ℂ] H
  pos : ∀ m, (E m).IsPositive
  hasSum_apply : ∀ x, HasSum (fun m => E m x) x

end QuantumTheory
