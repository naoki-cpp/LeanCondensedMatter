import LeanCondensedMatter.Analysis.Operator.Unbounded.ResolventCommutation
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Commutation of bounded resolvent approximations

The bounded self-adjoint approximants used in the Stone construction are symmetric linear
combinations of nonreal resolvents of one self-adjoint operator.  Since those resolvents commute
pairwise, the approximants commute at different regularization scales as well.
-/

namespace LinearPMap

noncomputable section

open Complex
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Bounded self-adjoint resolvent approximants at two positive scales commute. -/
theorem boundedSelfAdjointApproximation_commute
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (r s : ℝ) (hr : 0 < r) (hs : 0 < s) :
    Commute (boundedSelfAdjointApproximation A hA r hr)
      (boundedSelfAdjointApproximation A hA s hs) := by
  unfold boundedSelfAdjointApproximation
  apply Commute.smul_left
  apply Commute.smul_right
  apply Commute.add_left
  · apply Commute.add_right
    · apply nonrealResolvent_commute
    · apply nonrealResolvent_commute
  · apply Commute.add_right
    · apply nonrealResolvent_commute
    · apply nonrealResolvent_commute

/-- Equality form of bounded approximant commutation. -/
theorem boundedSelfAdjointApproximation_mul_comm
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (r s : ℝ) (hr : 0 < r) (hs : 0 < s) :
    boundedSelfAdjointApproximation A hA r hr *
        boundedSelfAdjointApproximation A hA s hs =
      boundedSelfAdjointApproximation A hA s hs *
        boundedSelfAdjointApproximation A hA r hr := by
  exact (boundedSelfAdjointApproximation_commute A hA r s hr hs).eq

end

end LinearPMap
