import LeanCondensedMatter.SecondQuantization.Bosonic.Algebra.CCR
import LeanCondensedMatter.SecondQuantization.Bosonic.ImaginaryTime.ImaginaryTimeEvolution

set_option linter.style.header false

/-!
# Free bosonic two-point basis coefficients

`diagonalCoeff A n` is the coefficient of `basisState n` in `A (basisState n)`. It is a coordinate
evaluation on the algebraic Fock space, not an inner product or operator trace.

The main results compute the coefficients of `a_i(τ) a_j†`: the equal-mode coefficient is
`e^{-τεᵢ}(n_i + 1)`, while distinct modes give zero.
-/

namespace SecondQuantization
namespace Bosonic

variable {Mode : Type*}

/-- The coefficient of `basisState n` in `A (basisState n)`. -/
noncomputable def diagonalCoeff (A : FockSpace Mode →ₗ[ℂ] FockSpace Mode)
    (n : Occupation Mode) : ℂ :=
  Common.diagonalCoeff A n

theorem diagonalCoeff_eq (A : FockSpace Mode →ₗ[ℂ] FockSpace Mode)
    (n : Occupation Mode) : diagonalCoeff A n = A (basisState n) n :=
  rfl

/-- The equal-mode coefficient is `e^{-τεᵢ}(n_i + 1)`. -/
theorem diagonalCoeff_evolve_annihilate_comp_create_same (ε : Mode → ℝ) (τ : ℝ) (i : Mode)
    (n : Occupation Mode) :
    diagonalCoeff (((imaginaryTimeEvolve ε τ (annihilate i)).comp (create i)))
      n = Complex.exp (-(τ : ℂ) * (ε i : ℂ)) * ((n i : ℂ) + 1) := by
  rw [diagonalCoeff_eq, LinearMap.comp_apply, imaginaryTimeEvolve_annihilate,
    LinearMap.smul_apply, annihilate_create_basisState_same, smul_smul, basisState,
    Common.smul_basisState_apply_self]

/-- The coefficient vanishes when the annihilation and creation modes are distinct. -/
theorem diagonalCoeff_evolve_annihilate_comp_create_of_ne (ε : Mode → ℝ) (τ : ℝ) {i j : Mode}
    (hij : i ≠ j) (n : Occupation Mode) :
    diagonalCoeff ((imaginaryTimeEvolve ε τ (annihilate i)).comp (create j)) n = 0 := by
  rw [diagonalCoeff_eq, LinearMap.comp_apply, imaginaryTimeEvolve_annihilate,
    LinearMap.smul_apply, create_basisState_eq, map_smul, Finsupp.smul_apply, smul_eq_mul]
  change Complex.exp (-(τ : ℂ) * (ε i : ℂ)) *
      ((Real.sqrt (n j + 1 : ℝ) : ℂ) *
        Common.matrixCoeff (annihilate i) n (createOccupation j n)) = 0
  rw [matrixCoeff_annihilate]
  have hne : n ≠ removeOccupation i (createOccupation j n) := by
    intro h
    have hj := congrArg (fun x : Occupation Mode => x j) h
    rw [removeOccupation_apply_ne (Ne.symm hij), createOccupation_apply_same] at hj
    omega
  rw [ite_eq_right hne, mul_zero, mul_zero]

end Bosonic
end SecondQuantization
