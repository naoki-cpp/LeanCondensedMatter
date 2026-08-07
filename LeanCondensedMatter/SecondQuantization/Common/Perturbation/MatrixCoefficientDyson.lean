import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.InteractionPicture
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option linter.style.header false

/-!
# First Dyson operator on an infinite configuration space

The existing finite operator integral reconstructs an algebraic-Fock operator by summing over every
output basis state, and therefore assumes `[Fintype Config]`.  That global enumeration is not
necessary for the interaction-picture integral of a fixed algebraic operator.

For each input basis state `n`, the vector `V (basisState n)` already has finite support because its
codomain is `AlgebraicFock Config = Config →₀ ℂ`.  Imaginary-time diagonal evolution changes only
the coefficients, not this support.  The first Dyson coefficient can therefore be reconstructed by
integrating over that finite support, even when `Config` itself is infinite.

No boundedness, completed-space convergence, or infinite Dyson-series convergence is asserted.
-/

namespace SecondQuantization
namespace Common

variable {Config : Type*}

/-- The first interaction-picture Dyson coefficient at a fixed pair of basis configurations. -/
noncomputable def firstDysonMatrixCoeff (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (τ : ℝ) (m n : Config) : ℂ :=
  - ∫ σ in (0 : ℝ)..τ, matrixCoeff (interactionPicture energy V σ) m n

@[simp]
theorem firstDysonMatrixCoeff_zero (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (m n : Config) :
    firstDysonMatrixCoeff energy V 0 m n = 0 := by
  simp [firstDysonMatrixCoeff]

/-- The first coefficient is the integral of the explicit interaction-picture phase times the
original matrix coefficient. -/
theorem firstDysonMatrixCoeff_eq_phase_integral (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (τ : ℝ) (m n : Config) :
    firstDysonMatrixCoeff energy V τ m n =
      - ∫ σ in (0 : ℝ)..τ,
          Complex.exp ((σ * (energy m - energy n) : ℝ) : ℂ) * matrixCoeff V m n := by
  unfold firstDysonMatrixCoeff
  apply congrArg Neg.neg
  exact intervalIntegral.integral_congr fun σ _ =>
    matrixCoeff_interactionPicture energy V σ m n

/-- Every first-order Dyson matrix coefficient is continuous in the upper imaginary-time bound. -/
theorem continuous_firstDysonMatrixCoeff (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (m n : Config) :
    Continuous (fun τ : ℝ => firstDysonMatrixCoeff energy V τ m n) := by
  unfold firstDysonMatrixCoeff
  exact (intervalIntegral.continuous_primitive
    (fun a b => intervalIntegrable_matrixCoeff_interactionPicture energy V m n a b) 0).neg

/-- The image of one basis state under the first Dyson coefficient.

Only the finite support of `V (basisState n)` is used; the ambient configuration type need not be
finite. -/
noncomputable def firstDysonBasis (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (τ : ℝ) (n : Config) :
    AlgebraicFock Config :=
  ∑ m in (V (basisState n)).support,
    firstDysonMatrixCoeff energy V τ m n • basisState m

/-- The first interaction-picture Dyson coefficient as a genuine algebraic-Fock operator on an
arbitrary configuration type. -/
noncomputable def firstDysonCoeff (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (τ : ℝ) :
    AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config :=
  Finsupp.lift (AlgebraicFock Config) ℂ Config (firstDysonBasis energy V τ)

@[simp]
theorem firstDysonCoeff_basisState (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (τ : ℝ) (n : Config) :
    firstDysonCoeff energy V τ (basisState n) = firstDysonBasis energy V τ n := by
  change Finsupp.lift _ ℂ _ (firstDysonBasis energy V τ) (Finsupp.single n 1) = _
  simp [Finsupp.lift_apply, Finsupp.sum_single_index]

@[simp]
theorem firstDysonCoeff_zero (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    firstDysonCoeff energy V 0 = 0 := by
  apply Finsupp.lhom_ext
  intro n c
  rw [firstDysonCoeff_basisState]
  simp [firstDysonBasis]

/-- The first Dyson image of `basisState n` is supported inside the original finite output support
of `V (basisState n)`. -/
theorem support_firstDysonCoeff_basisState_subset (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (τ : ℝ) (n : Config) :
    (firstDysonCoeff energy V τ (basisState n)).support ⊆ (V (basisState n)).support := by
  rw [firstDysonCoeff_basisState, firstDysonBasis]
  exact Finsupp.support_finsetSum_subset _ _

end Common
end SecondQuantization
