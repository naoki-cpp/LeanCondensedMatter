import LeanCondensedMatter.Analysis.Dyson.Bounds
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.ContinuousDyson

set_option linter.style.header false

/-!
# Finite specialization bridge for the generic Dyson core

This module identifies the transported finite-dimensional Dyson coefficients with the
state-independent recursion owned by `Analysis.Dyson`.  The finite layer retains only the
interaction-picture realization and its compatibility with the algebraic Fock-space construction.
-/

namespace SecondQuantization
namespace Common

noncomputable section

variable {Config : Type*} [Fintype Config]

/-- The transported finite-dimensional Dyson coefficient is exactly the generic bounded Dyson
coefficient specialized to the continuous interaction-picture family. -/
theorem continuousDysonCoeff_eq_coeff (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (n : ℕ) (τ : ℝ) :
    continuousDysonCoeff energy V n τ =
      Dyson.coeff (continuousInteractionPicture energy V) n τ := by
  induction n generalizing τ with
  | zero => simp
  | succ n ih =>
      rw [continuousDysonCoeff_succ, Dyson.coeff_succ]
      apply congrArg Neg.neg
      apply intervalIntegral.integral_congr
      intro σ _
      change continuousInteractionPicture energy V σ *
          continuousDysonCoeff energy V n σ =
        continuousInteractionPicture energy V σ *
          Dyson.coeff (continuousInteractionPicture energy V) n σ
      rw [ih]

end
end Common
end SecondQuantization
