import LeanCondensedMatter.SecondQuantization.Bosonic.Foundations.FockSpace
import LeanCondensedMatter.SecondQuantization.Common.TimeOrdering

set_option linter.style.header false

/-!
# Bosonic imaginary-time ordering

This module specializes `Common.timeOrderedProduct` to bosonic statistics and the algebraic bosonic
Fock space. Since the bosonic exchange sign is `+1`, swapping the operators introduces no scalar
factor in the public specialization.
-/

namespace SecondQuantization
namespace Bosonic

variable {Mode : Type*} [DecidableEq Mode]

/-- The bosonic imaginary-time-ordered product of two operators. -/
noncomputable def timeOrderedProduct
    (A B : FockSpace Mode →ₗ[ℂ] FockSpace Mode) (τA τB : ℝ) :
    FockSpace Mode →ₗ[ℂ] FockSpace Mode :=
  Common.timeOrderedProduct Statistics.boson A B τA τB

/-- At strictly later time, `A` acts first. -/
theorem timeOrderedProduct_of_gt
    (A B : FockSpace Mode →ₗ[ℂ] FockSpace Mode) {τA τB : ℝ} (h : τB < τA) :
    timeOrderedProduct A B τA τB = A.comp B :=
  Common.timeOrderedProduct_of_gt Statistics.boson A B h

/-- At strictly later time, `B` acts first without a bosonic exchange sign. -/
theorem timeOrderedProduct_of_lt
    (A B : FockSpace Mode →ₗ[ℂ] FockSpace Mode) {τA τB : ℝ} (h : τA < τB) :
    timeOrderedProduct A B τA τB = B.comp A := by
  simpa [timeOrderedProduct] using
    (Common.timeOrderedProduct_of_lt Statistics.boson A B h)

/-- Equal imaginary times give the symmetric product. -/
@[simp]
theorem timeOrderedProduct_self_time
    (A B : FockSpace Mode →ₗ[ℂ] FockSpace Mode) (τ : ℝ) :
    timeOrderedProduct A B τ τ = (2⁻¹ : ℂ) • (A.comp B + B.comp A) := by
  simpa [timeOrderedProduct] using
    (Common.timeOrderedProduct_self_time Statistics.boson A B τ)

/-- Swapping both operators and their times leaves the bosonic ordered product unchanged. -/
theorem timeOrderedProduct_swap
    (A B : FockSpace Mode →ₗ[ℂ] FockSpace Mode) (τA τB : ℝ) :
    timeOrderedProduct B A τB τA = timeOrderedProduct A B τA τB := by
  simpa [timeOrderedProduct] using
    (Common.timeOrderedProduct_swap Statistics.boson A B τA τB)

end Bosonic
end SecondQuantization
