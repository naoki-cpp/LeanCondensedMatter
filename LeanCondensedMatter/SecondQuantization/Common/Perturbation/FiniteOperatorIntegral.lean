import LeanCondensedMatter.SecondQuantization.Common.Algebra.DiagonalTrace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option linter.style.header false

/-!
# Coefficientwise interval integration of a finite-mode operator-valued function

`AlgebraicFock Config` is an algebraic vector space with no operator norm or Hilbert completion.
For finite `Config`, an operator-valued function can nevertheless be integrated coefficientwise:
for fixed configurations `m,n`, the matrix coefficient
`τ ↦ matrixCoeff (F τ) m n` is an ordinary complex-valued function.

`operatorIntervalIntegral F a b` is defined by these scalar interval integrals, and its matrix
coefficients are proved to agree exactly with them. This provides the finite-configuration
operator-integral realization used by the Dyson recursion without adding a topology to the
algebraic Fock space.
-/

namespace SecondQuantization
namespace Common

variable {Config : Type*} [Fintype Config]

/-- The image of a basis vector under the coefficientwise interval integral. -/
private noncomputable def operatorIntervalIntegralBasis
    (F : ℝ → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (a b : ℝ) (n : Config) :
    AlgebraicFock Config :=
  Finsupp.equivFunOnFinite.symm fun m => ∫ τ in a..b, matrixCoeff (F τ) m n

/-- **The coefficientwise interval integral** of an operator-valued function `F`, `∫ τ in a..b, F
τ`: the linear map sending `basisState n` to `operatorIntervalIntegralBasis F a b n`. -/
noncomputable def operatorIntervalIntegral
    (F : ℝ → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (a b : ℝ) :
    AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config :=
  Finsupp.lift (AlgebraicFock Config) ℂ Config (operatorIntervalIntegralBasis F a b)

/-- **The matrix-coefficient formula**: `operatorIntervalIntegral`'s own matrix coefficients are
exactly the scalar interval integrals of `F`'s matrix coefficients. -/
theorem matrixCoeff_operatorIntervalIntegral
    (F : ℝ → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (a b : ℝ) (m n : Config) :
    matrixCoeff (operatorIntervalIntegral F a b) m n = ∫ τ in a..b, matrixCoeff (F τ) m n := by
  have hbasis :
      operatorIntervalIntegral F a b (basisState n) = operatorIntervalIntegralBasis F a b n := by
    change Finsupp.lift _ ℂ _ (operatorIntervalIntegralBasis F a b) (Finsupp.single n 1) =
      operatorIntervalIntegralBasis F a b n
    simp [Finsupp.lift_apply, Finsupp.sum_single_index]
  rw [matrixCoeff, hbasis, operatorIntervalIntegralBasis]
  rfl

@[simp]
theorem operatorIntervalIntegral_zero (a b : ℝ) :
    operatorIntervalIntegral
      (fun _ : ℝ => (0 : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)) a b = 0 := by
  apply matrixCoeff_ext
  intro m n
  rw [matrixCoeff_operatorIntervalIntegral]
  simp [matrixCoeff]

@[simp]
theorem operatorIntervalIntegral_same
    (F : ℝ → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (a : ℝ) :
    operatorIntervalIntegral F a a = 0 := by
  apply matrixCoeff_ext
  intro m n
  rw [matrixCoeff_operatorIntervalIntegral, intervalIntegral.integral_same, matrixCoeff]
  simp

theorem operatorIntervalIntegral_add
    (F G : ℝ → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (a b : ℝ)
    (hF : ∀ m n, IntervalIntegrable (fun τ => matrixCoeff (F τ) m n) MeasureTheory.volume a b)
    (hG : ∀ m n, IntervalIntegrable (fun τ => matrixCoeff (G τ) m n) MeasureTheory.volume a b) :
    operatorIntervalIntegral (fun τ => F τ + G τ) a b =
      operatorIntervalIntegral F a b + operatorIntervalIntegral G a b := by
  apply matrixCoeff_ext
  intro m n
  simp only [← matrixCoeffLinear_apply, map_add]
  simp only [matrixCoeffLinear_apply, matrixCoeff_operatorIntervalIntegral]
  exact intervalIntegral.integral_add (hF m n) (hG m n)

theorem operatorIntervalIntegral_smul (c : ℂ)
    (F : ℝ → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (a b : ℝ) :
    operatorIntervalIntegral (fun τ => c • F τ) a b = c • operatorIntervalIntegral F a b := by
  apply matrixCoeff_ext
  intro m n
  simp only [← matrixCoeffLinear_apply, map_smul]
  simp only [matrixCoeffLinear_apply, smul_eq_mul, matrixCoeff_operatorIntervalIntegral]
  exact intervalIntegral.integral_const_mul _ _

/-- **Left-composition with a fixed operator commutes with `operatorIntervalIntegral`**:
`L ∘ (∫ F) = ∫ (L ∘ F)`, given interval-integrability of every matrix coefficient `F` contributes.
Both sides reduce, via `matrixCoeff_comp`/`matrixCoeff_operatorIntervalIntegral`, to the same
`∑ k, matrixCoeff L m k * ∫ σ, matrixCoeff (F σ) k n` vs. `∫ σ, ∑ k, matrixCoeff L m k *
matrixCoeff (F σ) k n` — the finite-sum/integral interchange `intervalIntegral.integral_finsetSum`
supplies, after pulling the constant `matrixCoeff L m k` in/out of each summand's integral
(`intervalIntegral.integral_const_mul`). Needed to move an already-evaluated interaction-picture
vertex factor past the ordered-simplex integral over the *remaining* Dyson coefficient. -/
theorem comp_operatorIntervalIntegral (L : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (F : ℝ → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (a b : ℝ)
    (hF : ∀ (k n : Config), IntervalIntegrable (fun σ => matrixCoeff (F σ) k n)
      MeasureTheory.volume a b) :
    L.comp (operatorIntervalIntegral F a b) = operatorIntervalIntegral (fun σ => L.comp (F σ)) a b
    := by
  apply matrixCoeff_ext
  intro m n
  simp only [matrixCoeff_comp, matrixCoeff_operatorIntervalIntegral]
  rw [intervalIntegral.integral_finsetSum fun k _ => (hF k n).const_mul (matrixCoeff L m k)]
  exact Finset.sum_congr rfl fun k _ => (intervalIntegral.integral_const_mul _ _).symm

end Common
end SecondQuantization
