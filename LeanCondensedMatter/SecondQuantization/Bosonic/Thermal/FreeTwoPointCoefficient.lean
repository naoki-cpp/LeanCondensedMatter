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
    LinearMap.smul_apply, create_basisState_eq, map_smul]
  by_cases hi : (createOccupation j n) i = 0
  · simp [annihilate_basisState_of_zero hi]
  · have hni : n i ≠ 0 := by rwa [createOccupation_apply_ne hij] at hi
    have hswap :
        removeOccupation i (createOccupation j n) = createOccupation j (removeOccupation i n) :=
      removeOccupation_createOccupation_of_ne hij n
    rw [annihilate_basisState_of_pos hi, smul_smul, smul_smul, hswap]
    have hne : createOccupation j (removeOccupation i n) ≠ n := by
      intro heq
      have hcoord := congrArg (· i) heq
      rw [createOccupation_apply_ne hij, removeOccupation_apply_same] at hcoord
      omega
    simp [basisState, Common.basisState, hne]

end Bosonic
end SecondQuantization
