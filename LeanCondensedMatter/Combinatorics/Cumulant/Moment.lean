import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Partition.Finpartition

set_option linter.style.header false

/-!
# Finite-set moment transform on the partition lattice

The moment transform only uses finite sums and products, so it is defined over a commutative
semiring. Möbius inversion, which needs additive inverses, lives separately in
`Combinatorics/Cumulant/Inversion.lean`.
-/

variable {α R : Type*} [DecidableEq α] [CommSemiring R]

namespace Finpartition

/-- Product of `f` over the blocks of a partition. -/
noncomputable def partitionProduct (f : Finset α → R) {S : Finset α} (π : Finpartition S) : R :=
  ∏ B ∈ π.parts, f B

/-- Moment transform of a finite-set cumulant function. -/
noncomputable def momentFromCumulant (κ : Finset α → R) (S : Finset α) : R :=
  ∑ π : Finpartition S, partitionProduct κ π

end Finpartition
