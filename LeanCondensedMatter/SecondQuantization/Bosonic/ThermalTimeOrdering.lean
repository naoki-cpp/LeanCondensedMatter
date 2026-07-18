import LeanCondensedMatter.SecondQuantization.Bosonic.FockSpace
import LeanCondensedMatter.SecondQuantization.Common.TimeOrdering

set_option linter.style.header false

/-!
# Imaginary-time ordering `T_τ`, specialized to the bosonic Fock space

The `ThermalTimeOrdering` filename is historical: this module defines imaginary-time ordering and
does not introduce a thermal state, weight, or inverse temperature.

The bosonic mirror of `Fermionic/ThermalTimeOrdering.lean`: a thin wrapper fixing
`Common/TimeOrdering.lean`'s `Common.timeOrderedProduct` to `FockSpaceBosonic Mode` *and* to
`Statistics.boson`. Nothing here is fermion-specific — the definition and every theorem below are
identical to the fermionic file up to the type of the operators and the sign (`+1` rather than
`-1`) — so this file exists purely for symmetry with the fermionic line's file layout
(`notes/roadmaps/second-quantization.md`'s `Common/` design principle), not because anything in
the bosonic line consumes `timeOrderedProduct` yet.
-/

namespace SecondQuantization
namespace Bosonic

variable {Mode : Type*} [DecidableEq Mode]

/-- **The imaginary-time-ordered product** of two operators `A`, `B` at imaginary times `τ_A`,
`τ_B`: the later time acts first (leftmost), picking up the bosonic exchange sign `+1` when the
times must be swapped from their given argument order, and the two orderings symmetrized
(`θ(0) = 1/2`) at equal times. -/
noncomputable def timeOrderedProduct
    (A B : FockSpaceBosonic Mode →ₗ[ℂ] FockSpaceBosonic Mode) (τA τB : ℝ) :
    FockSpaceBosonic Mode →ₗ[ℂ] FockSpaceBosonic Mode :=
  Common.timeOrderedProduct Statistics.boson A B τA τB

theorem timeOrderedProduct_of_gt
    (A B : FockSpaceBosonic Mode →ₗ[ℂ] FockSpaceBosonic Mode) {τA τB : ℝ} (h : τB < τA) :
    timeOrderedProduct A B τA τB = A.comp B :=
  Common.timeOrderedProduct_of_gt Statistics.boson A B h

theorem timeOrderedProduct_of_lt
    (A B : FockSpaceBosonic Mode →ₗ[ℂ] FockSpaceBosonic Mode) {τA τB : ℝ} (h : τA < τB) :
    timeOrderedProduct A B τA τB = (1 : ℂ) • (B.comp A) := by
  change Common.timeOrderedProduct Statistics.boson A B τA τB = (1 : ℂ) • (B.comp A)
  rw [Common.timeOrderedProduct_of_lt Statistics.boson A B h, Statistics.zetaInt_boson,
    Int.cast_one]

@[simp]
theorem timeOrderedProduct_self_time
    (A B : FockSpaceBosonic Mode →ₗ[ℂ] FockSpaceBosonic Mode) (τ : ℝ) :
    timeOrderedProduct A B τ τ = (2⁻¹ : ℂ) • (A.comp B + (1 : ℂ) • (B.comp A)) := by
  change Common.timeOrderedProduct Statistics.boson A B τ τ =
    (2⁻¹ : ℂ) • (A.comp B + (1 : ℂ) • (B.comp A))
  rw [Common.timeOrderedProduct_self_time Statistics.boson A B τ, Statistics.zetaInt_boson,
    Int.cast_one]

/-- **Swapping the pair of operators (with their times) returns the same time-ordered product**:
`T_τ[B(τ_B) A(τ_A)] = T_τ[A(τ_A) B(τ_B)]`. See `Common/TimeOrdering.lean`'s module docstring for
the scope note on which operators this applies to. -/
theorem timeOrderedProduct_swap
    (A B : FockSpaceBosonic Mode →ₗ[ℂ] FockSpaceBosonic Mode) (τA τB : ℝ) :
    timeOrderedProduct B A τB τA = (1 : ℂ) • timeOrderedProduct A B τA τB := by
  change Common.timeOrderedProduct Statistics.boson B A τB τA =
    (1 : ℂ) • Common.timeOrderedProduct Statistics.boson A B τA τB
  rw [Common.timeOrderedProduct_swap Statistics.boson A B τA τB, Statistics.zetaInt_boson,
    Int.cast_one]

end Bosonic
end SecondQuantization
