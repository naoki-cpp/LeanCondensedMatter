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

noncomputable section

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
  simp only [← matrixCoeffLinear_apply, map_neg]
  rw [matrixCoeffLinear_apply, matrixCoeff_operatorIntervalIntegral]
  congr 1

end

end Common
end SecondQuantization
