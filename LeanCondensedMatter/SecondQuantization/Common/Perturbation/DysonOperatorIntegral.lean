import LeanCondensedMatter.SecondQuantization.Common.Perturbation.DysonExpansion
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.FiniteOperatorIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

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

omit [Fintype Config] in
/-- In the time-independent case, each algebraic Dyson coefficient is the corresponding ordinary
exponential-series coefficient. -/
theorem dysonCoeff_eq_of_time_independent [Finite Config] (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (hV : ∀ τ, interactionPicture energy V τ = V) : ∀ (n : ℕ) (τ : ℝ),
    dysonCoeff energy V n τ = ((-τ : ℂ) ^ n / n.factorial) • V ^ n := by
  letI := Fintype.ofFinite Config
  intro n
  induction n with
  | zero => intro τ; simp [dysonCoeff_zero, Module.End.one_eq_id]
  | succ k ih =>
    intro τ
    rw [dysonCoeff_succ]
    have hcomp : V.comp (V ^ k) = V ^ (k + 1) := by
      rw [pow_succ', Module.End.mul_eq_comp]
    have hfun : (fun σ : ℝ => (interactionPicture energy V σ).comp
        (dysonCoeff energy V k σ)) = fun σ : ℝ =>
          (((-σ : ℂ) ^ k / k.factorial)) • V ^ (k + 1) := by
      funext σ
      rw [hV σ, ih σ, LinearMap.comp_smul, hcomp]
    rw [hfun]
    have hval : operatorIntervalIntegral
        (fun σ : ℝ => (((-σ : ℂ) ^ k / k.factorial)) • V ^ (k + 1)) 0 τ =
        (∫ σ in (0 : ℝ)..τ, ((-σ : ℂ) ^ k / k.factorial)) • V ^ (k + 1) := by
      apply matrixCoeff_ext
      intro m n'
      rw [matrixCoeff_operatorIntervalIntegral]
      simp only [← matrixCoeffLinear_apply, map_smul, smul_eq_mul]
      rw [intervalIntegral.integral_mul_const]
    rw [hval]
    have hpow : (∫ σ in (0 : ℝ)..τ, (-σ) ^ k) = -(-τ) ^ (k + 1) / (k + 1) := by
      have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := τ)
        (fun x : ℝ => x ^ k)
      simp only [neg_zero] at h
      rw [h, integral_pow, zero_pow (Nat.succ_ne_zero k)]
      ring
    have hcint : (∫ σ in (0 : ℝ)..τ, ((-σ : ℂ)) ^ k / (k.factorial : ℂ)) =
        - ((-τ : ℂ) ^ (k + 1) / ((k + 1).factorial : ℂ)) := by
      rw [intervalIntegral.integral_div]
      have hcast : (∫ σ in (0 : ℝ)..τ, ((-σ : ℂ)) ^ k) =
          ((∫ σ in (0 : ℝ)..τ, (-σ) ^ k : ℝ) : ℂ) := by
        rw [← intervalIntegral.integral_ofReal]
        apply intervalIntegral.integral_congr
        intro σ _
        push_cast
        ring
      rw [hcast, hpow, Nat.factorial_succ]
      push_cast
      field_simp
    rw [hcint, neg_smul, neg_neg]

end

end Common
end SecondQuantization
