import LeanCondensedMatter.SecondQuantization.Common.Perturbation.DysonExpansion
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.FiniteOperatorIntegral

set_option linter.style.header false

/-!
# Finite Dyson operator-integral identities

This module connects the generic Dyson coefficients to the coefficientwise operator-valued
integral when the configuration type is finite. Keeping these identities here leaves
`DysonExpansion` independent of the finite operator-integral construction.
-/

namespace SecondQuantization
namespace Common

variable {Config : Type*} [Fintype Config]

/-- On a finite configuration type, the canonical reachable-support coefficient satisfies the
operator-valued Dyson recursion reconstructed by `operatorIntervalIntegral`. -/
theorem dysonCoeff_succ (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (n : ℕ) (τ : ℝ) :
    dysonCoeff energy V (n + 1) τ =
      - operatorIntervalIntegral
          (fun σ => (interactionPicture energy V σ).comp (dysonCoeff energy V n σ)) 0 τ := by
  apply matrixCoeff_ext
  intro m n'
  change dysonCoeff energy V (n + 1) τ (basisState n') m =
    matrixCoeff
      (- operatorIntervalIntegral
        (fun σ => (interactionPicture energy V σ).comp (dysonCoeff energy V n σ)) 0 τ) m n'
  rw [dysonCoeff_succ_basisState_apply]
  have hneg : matrixCoeff
      (- operatorIntervalIntegral
          (fun σ => (interactionPicture energy V σ).comp (dysonCoeff energy V n σ)) 0 τ) m n' =
        - matrixCoeff (operatorIntervalIntegral
          (fun σ => (interactionPicture energy V σ).comp (dysonCoeff energy V n σ)) 0 τ) m n' := by
    simp [matrixCoeff]
  rw [hneg, matrixCoeff_operatorIntervalIntegral]
  congr 1

/-- The first-order coefficient is the negative interval integral of the interaction-picture
operator. -/
theorem dysonCoeff_one (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (τ : ℝ) :
    dysonCoeff energy V 1 τ = - operatorIntervalIntegral (interactionPicture energy V) 0 τ := by
  rw [show 1 = 0 + 1 by omega, dysonCoeff_succ]
  congr 2
  funext σ
  rw [dysonCoeff_zero, LinearMap.comp_id]

/-- Matrix-coefficient form of the finite Dyson successor recursion. -/
theorem matrixCoeff_dysonCoeff_succ (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (n : ℕ) (τ : ℝ)
    (m n' : Config) :
    matrixCoeff (dysonCoeff energy V (n + 1) τ) m n' =
      - ∫ σ in (0 : ℝ)..τ, ∑ k : Config,
          matrixCoeff (interactionPicture energy V σ) m k *
            matrixCoeff (dysonCoeff energy V n σ) k n' := by
  rw [dysonCoeff_succ]
  have hneg : matrixCoeff
      (- operatorIntervalIntegral
          (fun σ => (interactionPicture energy V σ).comp (dysonCoeff energy V n σ)) 0 τ) m n' =
        - matrixCoeff (operatorIntervalIntegral
          (fun σ => (interactionPicture energy V σ).comp (dysonCoeff energy V n σ)) 0 τ) m n' := by
    simp [matrixCoeff]
  rw [hneg, matrixCoeff_operatorIntervalIntegral]
  congr 1
  exact intervalIntegral.integral_congr fun σ _ => matrixCoeff_comp _ _ m n'

end Common
end SecondQuantization
