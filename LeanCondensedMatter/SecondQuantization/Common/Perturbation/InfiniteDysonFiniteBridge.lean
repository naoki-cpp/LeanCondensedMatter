import LeanCondensedMatter.SecondQuantization.Common.Perturbation.InfiniteDyson
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.DysonExpansion

set_option linter.style.header false

/-!
# Finite-configuration bridge for the infinite-configuration Dyson recursion

When the ambient configuration type is finite, the reachable-support reconstruction from
`InfiniteDyson` agrees exactly with the older globally reconstructed finite-basis coefficient
`dysonCoeff`.  This provides a regression bridge between the two implementations.
-/

namespace SecondQuantization
namespace Common

variable {Config : Type*} [Fintype Config]

/-- On a finite configuration type, the finite-reachable-support Dyson coefficient agrees with the
existing globally reconstructed finite-basis Dyson coefficient at every finite order. -/
theorem infiniteDysonCoeff_eq_dysonCoeff (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    ∀ order τ, infiniteDysonCoeff energy V order τ = dysonCoeff energy V order τ := by
  intro order
  induction order with
  | zero =>
      intro τ
      simp
  | succ order ih =>
      intro τ
      apply matrixCoeff_ext
      intro m n
      change infiniteDysonCoeff energy V (order + 1) τ (basisState n) m =
        matrixCoeff (dysonCoeff energy V (order + 1) τ) m n
      rw [infiniteDysonCoeff_succ_basisState_apply, matrixCoeff_dysonCoeff_succ]
      congr 1
      apply intervalIntegral.integral_congr
      intro σ _
      rw [ih σ]
      change interactionPicture energy V σ (dysonCoeff energy V order σ (basisState n)) m = _
      change matrixCoeff ((interactionPicture energy V σ).comp (dysonCoeff energy V order σ)) m n = _
      exact matrixCoeff_comp _ _ m n

/-- The arbitrary-configuration construction inherits continuity of every matrix coefficient in the
finite-configuration specialization. -/
theorem continuous_matrixCoeff_infiniteDysonCoeff_of_fintype (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (order : ℕ) (m n : Config) :
    Continuous (fun τ : ℝ => matrixCoeff (infiniteDysonCoeff energy V order τ) m n) := by
  simpa only [infiniteDysonCoeff_eq_dysonCoeff energy V order] using
    continuous_matrixCoeff_dysonCoeff energy V order m n

/-- The arbitrary-configuration construction inherits interval-integrability of every matrix
coefficient in the finite-configuration specialization. -/
theorem intervalIntegrable_matrixCoeff_infiniteDysonCoeff_of_fintype (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (order : ℕ)
    (m n : Config) (a b : ℝ) :
    IntervalIntegrable (fun τ : ℝ => matrixCoeff (infiniteDysonCoeff energy V order τ) m n)
      MeasureTheory.volume a b :=
  (continuous_matrixCoeff_infiniteDysonCoeff_of_fintype energy V order m n).intervalIntegrable a b

end Common
end SecondQuantization
