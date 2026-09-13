import LeanCondensedMatter.SecondQuantization.Common.Perturbation.FiniteAnalyticBridge
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.DysonExpansion

set_option linter.style.header false

/-!
# Continuous finite-dimensional realization of the Common Dyson construction

This module promotes the statistics-independent finite-configuration operators to Mathlib's
normed continuous-operator algebra on `FiniteAnalyticFock Config = Config → ℂ`.

The algebraic definitions remain authoritative. The continuous operators below are transported
images of `diagonalEvolution`, `interactionPicture`, and `dysonCoeff`; the Dyson successor equation
is obtained from the existing coefficientwise recursion through
`continuousOperatorIntervalIntegral_eq`, not redefined analytically.
-/

namespace SecondQuantization
namespace Common

noncomputable section

variable {Config : Type*} [Fintype Config]

/-! ## Continuous free evolution and interaction picture -/

/-- The transported continuous realization of `diagonalEvolution`. -/
noncomputable def continuousDiagonalEvolution (energy : Config → ℝ) (τ : ℝ) :
    FiniteContinuousOperator Config :=
  finiteContinuousOperator (diagonalEvolution energy τ)

@[simp]
theorem continuousDiagonalEvolution_basis_apply (energy : Config → ℝ) (τ : ℝ)
    (n : Config) :
    continuousDiagonalEvolution energy τ (finiteAnalyticBasis n) =
      Complex.exp ((τ * energy n : ℝ) : ℂ) • finiteAnalyticBasis n := by
  calc
    continuousDiagonalEvolution energy τ (finiteAnalyticBasis n) =
        finiteAnalyticFockEquiv
          (diagonalEvolution energy τ (basisState n)) := by
      rw [continuousDiagonalEvolution, ← finiteAnalyticFockEquiv_basisState,
        finiteContinuousOperator_equiv_apply]
    _ = Complex.exp ((τ * energy n : ℝ) : ℂ) • finiteAnalyticBasis n := by
      rw [diagonalEvolution_basisState, map_smul, finiteAnalyticFockEquiv_basisState]

@[simp]
theorem continuousDiagonalEvolution_zero (energy : Config → ℝ) :
    continuousDiagonalEvolution energy 0 = 1 := by
  rw [continuousDiagonalEvolution, diagonalEvolution_zero, finiteContinuousOperator_id]
  rfl

theorem continuousDiagonalEvolution_add (energy : Config → ℝ) (τ τ' : ℝ) :
    (continuousDiagonalEvolution energy τ).comp
        (continuousDiagonalEvolution energy τ') =
      continuousDiagonalEvolution energy (τ + τ') := by
  rw [continuousDiagonalEvolution, continuousDiagonalEvolution,
    continuousDiagonalEvolution, ← finiteContinuousOperator_comp,
    diagonalEvolution_add]

@[simp]
theorem continuousDiagonalEvolution_comp_neg (energy : Config → ℝ) (τ : ℝ) :
    (continuousDiagonalEvolution energy τ).comp
        (continuousDiagonalEvolution energy (-τ)) = 1 := by
  rw [continuousDiagonalEvolution, continuousDiagonalEvolution,
    ← finiteContinuousOperator_comp, diagonalEvolution_comp_neg,
    finiteContinuousOperator_id]
  rfl

@[simp]
theorem continuousDiagonalEvolution_neg_comp (energy : Config → ℝ) (τ : ℝ) :
    (continuousDiagonalEvolution energy (-τ)).comp
        (continuousDiagonalEvolution energy τ) = 1 := by
  rw [continuousDiagonalEvolution, continuousDiagonalEvolution,
    ← finiteContinuousOperator_comp, diagonalEvolution_neg_comp,
    finiteContinuousOperator_id]
  rfl

/-- The transported continuous interaction-picture operator. -/
noncomputable def continuousInteractionPicture (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (τ : ℝ) :
    FiniteContinuousOperator Config :=
  finiteContinuousOperator (interactionPicture energy V τ)

@[simp]
theorem continuousInteractionPicture_basis_apply_apply (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (τ : ℝ) (m n : Config) :
    continuousInteractionPicture energy V τ (finiteAnalyticBasis n) m =
      Complex.exp ((τ * (energy m - energy n) : ℝ) : ℂ) * matrixCoeff V m n := by
  rw [continuousInteractionPicture, finiteContinuousOperator_basis_apply,
    matrixCoeff_interactionPicture]

@[simp]
theorem continuousInteractionPicture_zero (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    continuousInteractionPicture energy V 0 = finiteContinuousOperator V := by
  simp [continuousInteractionPicture]

/-- The continuous interaction-picture family is continuous in imaginary time. -/
theorem continuous_continuousInteractionPicture (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    Continuous (continuousInteractionPicture energy V) := by
  apply continuous_finiteContinuousOperator
  intro m n
  exact continuous_matrixCoeff_interactionPicture energy V m n

/-- Continuous interaction-picture conjugation is composition by the transported free
 evolutions. -/
theorem continuousInteractionPicture_eq_conj (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (τ : ℝ) :
    continuousInteractionPicture energy V τ =
      (continuousDiagonalEvolution energy τ).comp
        ((finiteContinuousOperator V).comp
          (continuousDiagonalEvolution energy (-τ))) := by
  simp [continuousInteractionPicture, interactionPicture, heisenbergEvolve,
    continuousDiagonalEvolution]

/-! ## Continuous Dyson coefficients -/

/-- The transported continuous realization of the algebraic Dyson coefficient. -/
noncomputable def continuousDysonCoeff (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (n : ℕ) (τ : ℝ) :
    FiniteContinuousOperator Config :=
  finiteContinuousOperator (dysonCoeff energy V n τ)

/-- Each continuous Dyson coefficient is a continuous operator-valued function of imaginary
 time. -/
theorem continuous_continuousDysonCoeff (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (n : ℕ) :
    Continuous (continuousDysonCoeff energy V n) := by
  apply continuous_finiteContinuousOperator
  exact continuous_matrixCoeff_dysonCoeff energy V n

@[simp]
theorem continuousDysonCoeff_zero (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (τ : ℝ) :
    continuousDysonCoeff energy V 0 τ = 1 := by
  rw [continuousDysonCoeff, dysonCoeff_zero, finiteContinuousOperator_id]
  rfl

@[simp]
theorem continuousDysonCoeff_at_zero (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (n : ℕ) :
    continuousDysonCoeff energy V n 0 = if n = 0 then 1 else 0 := by
  rw [continuousDysonCoeff, dysonCoeff_at_zero]
  by_cases h : n = 0
  · rw [if_pos h, if_pos h, finiteContinuousOperator_id]
    rfl
  · rw [if_neg h, if_neg h, finiteContinuousOperator_zero]

/-- The algebraic Dyson recursion transported to Mathlib's Bochner interval integral. -/
theorem continuousDysonCoeff_succ (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (n : ℕ) (τ : ℝ) :
    continuousDysonCoeff energy V (n + 1) τ =
      - ∫ σ in (0 : ℝ)..τ,
          (continuousInteractionPicture energy V σ).comp
            (continuousDysonCoeff energy V n σ) := by
  have hcoeff : ∀ m n' : Config, Continuous (fun σ : ℝ =>
      matrixCoeff ((interactionPicture energy V σ).comp
        (dysonCoeff energy V n σ)) m n') := by
    intro m n'
    simp only [matrixCoeff_comp]
    exact continuous_finsetSum _ fun k _ =>
      (continuous_matrixCoeff_interactionPicture energy V m k).mul
        (continuous_matrixCoeff_dysonCoeff energy V n k n')
  rw [continuousDysonCoeff, dysonCoeff_succ, finiteContinuousOperator_neg,
    continuousOperatorIntervalIntegral_eq _ hcoeff]
  apply congrArg Neg.neg
  apply intervalIntegral.integral_congr
  intro σ _
  simp only [continuousInteractionPicture, continuousDysonCoeff,
    finiteContinuousOperator_comp]

end
end Common
end SecondQuantization
