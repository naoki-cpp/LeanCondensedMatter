import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.InteractionPicture
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.FiniteOperatorIntegral

set_option linter.style.header false

/-!
# Finite-configuration Dyson-series coefficients

For a finite configuration type with a basis-diagonal free energy, this file defines the
statistics-independent interaction-picture Dyson recursion

`D₀(τ) = id`,  `Dₙ₊₁(τ) = -∫ σ in 0..τ, V_I(σ) ∘ Dₙ(σ)`.

The construction is algebraic: operator integration is reconstructed coefficientwise from the
ordinary interval integrals of matrix coefficients. No norm, topology, convergence of an infinite
Dyson series, or identification with an operator exponential is asserted here.
-/

namespace SecondQuantization
namespace Common

variable {Config : Type*} [Fintype Config]

/-- The `n`-th Dyson coefficient for a finite basis-diagonal free energy. -/
noncomputable def dysonCoeff (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    ℕ → ℝ → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config
  | 0, _ => LinearMap.id
  | n + 1, τ =>
      - operatorIntervalIntegral
          (fun σ => (interactionPicture energy V σ).comp (dysonCoeff energy V n σ)) 0 τ

theorem dysonCoeff_zero (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (τ : ℝ) :
    dysonCoeff energy V 0 τ = LinearMap.id := rfl

theorem dysonCoeff_succ (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (n : ℕ) (τ : ℝ) :
    dysonCoeff energy V (n + 1) τ =
      - operatorIntervalIntegral
          (fun σ => (interactionPicture energy V σ).comp (dysonCoeff energy V n σ)) 0 τ := rfl

/-- The first-order coefficient is the negative interval integral of the interaction-picture
operator. -/
theorem dysonCoeff_one (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (τ : ℝ) :
    dysonCoeff energy V 1 τ = - operatorIntervalIntegral (interactionPicture energy V) 0 τ := by
  rw [dysonCoeff_succ]
  congr 2

/-- At zero imaginary time, only the zeroth Dyson coefficient is nonzero. -/
theorem dysonCoeff_at_zero (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (n : ℕ) :
    dysonCoeff energy V n 0 = if n = 0 then LinearMap.id else 0 := by
  cases n with
  | zero => simp [dysonCoeff_zero]
  | succ k => simp [dysonCoeff_succ, operatorIntervalIntegral_same]

/-- Matrix-coefficient form of the Dyson successor recursion. -/
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

/-- Every matrix coefficient of a finite Dyson coefficient is continuous in imaginary time. -/
theorem continuous_matrixCoeff_dysonCoeff (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (n : ℕ) :
    ∀ m n' : Config, Continuous (fun τ : ℝ => matrixCoeff (dysonCoeff energy V n τ) m n') := by
  induction n with
  | zero =>
    intro m n'
    simp only [dysonCoeff_zero]
    exact continuous_const
  | succ k ih =>
    intro m n'
    simp only [matrixCoeff_dysonCoeff_succ]
    have hcont : Continuous (fun σ : ℝ => ∑ k' : Config,
        matrixCoeff (interactionPicture energy V σ) m k' *
          matrixCoeff (dysonCoeff energy V k σ) k' n') :=
      continuous_finsetSum _ fun k' _ =>
        (continuous_matrixCoeff_interactionPicture energy V m k').mul (ih k' n')
    exact (intervalIntegral.continuous_primitive (fun a b => hcont.intervalIntegrable a b) 0).neg

/-- Every matrix coefficient of a finite Dyson coefficient is interval-integrable. -/
theorem intervalIntegrable_matrixCoeff_dysonCoeff (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (n : ℕ)
    (m n' : Config) (a b : ℝ) :
    IntervalIntegrable (fun τ : ℝ => matrixCoeff (dysonCoeff energy V n τ) m n')
      MeasureTheory.volume a b :=
  (continuous_matrixCoeff_dysonCoeff energy V n m n').intervalIntegrable a b

/-- The order-`N` finite Dyson truncation in the perturbation parameter `lam`. -/
noncomputable def dysonTruncation (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (lam : ℂ) (N : ℕ) (τ : ℝ) :
    AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config :=
  ∑ n ∈ Finset.range (N + 1), lam ^ n • dysonCoeff energy V n τ

end Common
end SecondQuantization
