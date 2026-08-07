import LeanCondensedMatter.SecondQuantization.Common.Perturbation.InfiniteDyson
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.DysonExpansion

set_option linter.style.header false

/-!
# Finite-configuration bridge for the infinite-configuration Dyson recursion

When the ambient configuration type is finite, the reachable-support reconstruction from
`InfiniteDyson` agrees exactly with the older globally reconstructed finite-basis coefficient
`dysonCoeff`. This provides a regression bridge between the two implementations.
-/

namespace SecondQuantization
namespace Common

variable {Config : Type*}

/-- On a finite configuration type, the finite-reachable-support Dyson coefficient agrees with the
existing globally reconstructed finite-basis Dyson coefficient at every finite order. -/
theorem infiniteDysonCoeff_eq_dysonCoeff [Fintype Config] (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    ∀ order τ, infiniteDysonCoeff energy V order τ = dysonCoeff energy V order τ := by
  intro order
  induction order with
  | zero =>
      intro τ
      rw [infiniteDysonCoeff_zero, dysonCoeff_zero]
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
      simp_rw [ih σ]
      change interactionPicture energy V σ (dysonCoeff energy V order σ (basisState n)) m = _
      change matrixCoeff ((interactionPicture energy V σ).comp (dysonCoeff energy V order σ)) m n = _
      exact matrixCoeff_comp _ _ m n

/-- On any finite configuration type, every matrix coefficient of the reachable-support Dyson
construction is continuous in imaginary time. -/
theorem continuous_matrixCoeff_infiniteDysonCoeff_of_finite [Finite Config]
    (energy : Config → ℝ) (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (order : ℕ) (m n : Config) :
    Continuous (fun τ : ℝ => matrixCoeff (infiniteDysonCoeff energy V order τ) m n) := by
  letI := Fintype.ofFinite Config
  simpa only [infiniteDysonCoeff_eq_dysonCoeff energy V order] using
    continuous_matrixCoeff_dysonCoeff energy V order m n

/-- On any finite configuration type, every matrix coefficient of the reachable-support Dyson
construction is interval-integrable. -/
theorem intervalIntegrable_matrixCoeff_infiniteDysonCoeff_of_finite [Finite Config]
    (energy : Config → ℝ) (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (order : ℕ)
    (m n : Config) (a b : ℝ) :
    IntervalIntegrable (fun τ : ℝ => matrixCoeff (infiniteDysonCoeff energy V order τ) m n)
      MeasureTheory.volume a b :=
  (continuous_matrixCoeff_infiniteDysonCoeff_of_finite energy V order m n).intervalIntegrable a b

end Common
end SecondQuantization
