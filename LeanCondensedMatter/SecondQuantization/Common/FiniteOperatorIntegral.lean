import LeanCondensedMatter.SecondQuantization.Common.AlgebraicFock
import LeanCondensedMatter.SecondQuantization.Common.WeightedDiagonalFunctional
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option linter.style.header false

/-!
# Coefficientwise interval integration of a finite-mode operator-valued function

Groundwork for the genuine (continuous imaginary-time) interaction-picture Dyson series
(`notes/roadmaps/second-quantization.md`, Phase 9, step 5): `AlgebraicFock Config` is a purely
algebraic vector space (finite `ℂ`-linear combinations of basis states, no topology, no inner
product — see `AlgebraicFock.lean`'s module docstring), so there is no norm on operators to
integrate an operator-valued function against directly. Rather than introducing one, this file
exploits `[Fintype Config]`: an operator-valued function `F : ℝ → AlgebraicFock Config →ₗ[ℂ]
AlgebraicFock Config` has, for each fixed `m n : Config`, an ordinary `ℂ`-valued matrix-coefficient
function `τ ↦ matrixCoeff (F τ) m n`, integrable by Mathlib's `intervalIntegral` directly.
`operatorIntervalIntegral F a b` is defined so that its own matrix coefficients are exactly those
scalar integrals (`matrixCoeff_operatorIntervalIntegral`) — a genuine continuous integral, built
without adding any norm/topology to `AlgebraicFock Config` itself.
-/

namespace SecondQuantization
namespace Common

variable {Config : Type*} [Fintype Config]

/-- **The image of a basis vector** under the coefficientwise interval integral: `∑ m, (∫ τ in
a..b, matrixCoeff (F τ) m n) • basisState m`. -/
noncomputable def operatorIntervalIntegralBasis
    (F : ℝ → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (a b : ℝ) (n : Config) :
    AlgebraicFock Config :=
  ∑ m : Config, (∫ τ in a..b, matrixCoeff (F τ) m n) • basisState m

/-- **The coefficientwise interval integral** of an operator-valued function `F`, `∫ τ in a..b, F
τ`: the linear map sending `basisState n` to `operatorIntervalIntegralBasis F a b n`. -/
noncomputable def operatorIntervalIntegral
    (F : ℝ → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (a b : ℝ) :
    AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config :=
  Finsupp.lift (AlgebraicFock Config) ℂ Config (operatorIntervalIntegralBasis F a b)

theorem operatorIntervalIntegral_basisState
    (F : ℝ → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (a b : ℝ) (n : Config) :
    operatorIntervalIntegral F a b (basisState n) = operatorIntervalIntegralBasis F a b n := by
  change Finsupp.lift _ ℂ _ (operatorIntervalIntegralBasis F a b) (Finsupp.single n 1) =
    operatorIntervalIntegralBasis F a b n
  simp [Finsupp.lift_apply, Finsupp.sum_single_index]

/-- **The matrix-coefficient formula**: `operatorIntervalIntegral`'s own matrix coefficients are
exactly the scalar interval integrals of `F`'s matrix coefficients. -/
theorem matrixCoeff_operatorIntervalIntegral
    (F : ℝ → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (a b : ℝ) (m n : Config) :
    matrixCoeff (operatorIntervalIntegral F a b) m n = ∫ τ in a..b, matrixCoeff (F τ) m n := by
  rw [matrixCoeff, operatorIntervalIntegral_basisState, operatorIntervalIntegralBasis,
    Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single m]
  · exact smul_basisState_apply_self _ m
  · intro m' _ hne
    exact smul_basisState_apply_of_ne _ hne
  · intro h
    exact absurd (Finset.mem_univ m) h

omit [Fintype Config] in
/-- **Two operators agreeing on every matrix coefficient are equal.** Used repeatedly below to
reduce operator equalities to scalar (matrix-coefficient) ones. -/
theorem matrixCoeff_ext {A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config}
    (h : ∀ m n, matrixCoeff A m n = matrixCoeff B m n) : A = B := by
  apply linearMap_ext_basisState
  intro n
  apply Finsupp.ext
  intro m
  exact h m n

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
  have hL : matrixCoeff (operatorIntervalIntegral (fun τ => F τ + G τ) a b) m n =
      ∫ τ in a..b, (matrixCoeff (F τ) m n + matrixCoeff (G τ) m n) := by
    rw [matrixCoeff_operatorIntervalIntegral]
    exact intervalIntegral.integral_congr fun τ _ => matrixCoeff_add (F τ) (G τ) m n
  rw [hL, matrixCoeff_add, matrixCoeff_operatorIntervalIntegral,
    matrixCoeff_operatorIntervalIntegral, intervalIntegral.integral_add (hF m n) (hG m n)]

theorem operatorIntervalIntegral_smul (c : ℂ)
    (F : ℝ → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (a b : ℝ) :
    operatorIntervalIntegral (fun τ => c • F τ) a b = c • operatorIntervalIntegral F a b := by
  apply matrixCoeff_ext
  intro m n
  have hL : matrixCoeff (operatorIntervalIntegral (fun τ => c • F τ) a b) m n =
      ∫ τ in a..b, c * matrixCoeff (F τ) m n := by
    rw [matrixCoeff_operatorIntervalIntegral]
    exact intervalIntegral.integral_congr fun τ _ => matrixCoeff_smul c (F τ) m n
  rw [hL, matrixCoeff_smul, intervalIntegral.integral_const_mul,
    matrixCoeff_operatorIntervalIntegral]

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

/-! ## Interaction with a finite weighted trace/normalized diagonal functional -/

/-- **A weighted trace commutes with `operatorIntervalIntegral`**: `Tr_w[∫ F] = ∫ Tr_w[F]`, given
interval-integrability of every matrix coefficient `F` contributes to the (finite) weighted-trace
sum. Combines `matrixCoeff_operatorIntervalIntegral` (pushing the integral inside each summand)
with `intervalIntegral.integral_finsetSum` (swapping the now-finite `Config`-indexed sum with the
integral) — the finite-sum interchange PR 6's ordered-simplex reduction of `dysonCoeff` needs. -/
theorem weightedTrace_operatorIntervalIntegral (w : Config → ℂ)
    (F : ℝ → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (a b : ℝ)
    (hF : ∀ n : Config, IntervalIntegrable (fun τ => matrixCoeff (F τ) n n) MeasureTheory.volume
      a b) :
    weightedTrace w (operatorIntervalIntegral F a b) =
      ∫ τ in a..b, weightedTrace w (F τ) := by
  simp only [weightedTrace]
  have hstep : ∀ n : Config, w n * matrixCoeff (operatorIntervalIntegral F a b) n n =
      ∫ τ in a..b, w n * matrixCoeff (F τ) n n := by
    intro n
    rw [matrixCoeff_operatorIntervalIntegral, intervalIntegral.integral_const_mul]
  simp_rw [hstep]
  exact (intervalIntegral.integral_finsetSum fun n _ => (hF n).const_mul (w n)).symm

/-- **A normalized weighted diagonal functional commutes with `operatorIntervalIntegral`**,
dividing `weightedTrace_operatorIntervalIntegral` through by the (`τ`-independent) `weightSum w`
via `intervalIntegral.integral_div`. -/
theorem normalizedWeightedDiagonal_operatorIntervalIntegral (w : Config → ℂ)
    (F : ℝ → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (a b : ℝ)
    (hF : ∀ n : Config, IntervalIntegrable (fun τ => matrixCoeff (F τ) n n) MeasureTheory.volume
      a b) :
    normalizedWeightedDiagonal w (operatorIntervalIntegral F a b) =
      ∫ τ in a..b, normalizedWeightedDiagonal w (F τ) := by
  simp only [normalizedWeightedDiagonal]
  rw [weightedTrace_operatorIntervalIntegral w F a b hF, intervalIntegral.integral_div]

end Common
end SecondQuantization
