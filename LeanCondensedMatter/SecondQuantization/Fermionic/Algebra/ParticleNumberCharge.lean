import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.CreationAnnihilation
import LeanCondensedMatter.SecondQuantization.Common.Algebra.ParticleNumberSelectionRule

set_option linter.style.header false

/-!
# Fermionic particle-number charge

This module instantiates `Common.CarriesGradingDegree` for fermionic creation and annihilation
operators, with the occupation particle number as grading. An annihilation operator carries degree
`-1`, while a creation operator carries degree `+1`.

As an algebraic consequence, products of two annihilation operators or two creation operators carry
nonzero degree and therefore have vanishing diagonal occupation-basis coefficients. Thermal modules
may lift these basis-level statements to weighted traces and time-ordered correlators.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode]

/-- **`annihilate i` carries particle-number charge `-1`**: it only ever connects a basis state
`m` to a basis state `n` with one fewer particle, `particleNumber m = particleNumber
n - 1`. -/
theorem carriesParticleNumberCharge_annihilate (i : Mode) :
    Common.CarriesGradingDegree
      (fun n : Occupation Mode => (particleNumber n : ℤ)) (annihilate i) (-1) := by
  intro m n hmn
  change annihilate i (basisState n) m ≠ 0 at hmn
  by_cases hi : i ∈ n
  · rw [annihilate_basisState_of_mem hi] at hmn
    by_cases hm : m = removeOccupation i n
    · have hcard := particleNumber_removeOccupation_of_mem hi
      rw [hm]
      change (particleNumber (removeOccupation i n) : ℤ) =
        (particleNumber n : ℤ) + (-1)
      omega
    · exact absurd (Common.smul_basisState_apply_of_ne _ (Ne.symm hm)) hmn
  · rw [annihilate_basisState_of_not_mem hi] at hmn
    simp at hmn

/-- **`create i` carries particle-number charge `+1`**: it only ever connects a basis state `m` to
a basis state `n` with one more particle, `particleNumber m = particleNumber n +
1`. -/
theorem carriesParticleNumberCharge_create (i : Mode) :
    Common.CarriesGradingDegree
      (fun n : Occupation Mode => (particleNumber n : ℤ)) (create i) 1 := by
  intro m n hmn
  change create i (basisState n) m ≠ 0 at hmn
  by_cases hi : i ∈ n
  · rw [create_basisState_of_mem hi] at hmn
    simp at hmn
  · rw [create_basisState_of_not_mem hi] at hmn
    by_cases hm : m = insertOccupation i n
    · have hcard := particleNumber_insertOccupation_of_not_mem hi
      rw [hm]
      change (particleNumber (insertOccupation i n) : ℤ) =
        (particleNumber n : ℤ) + 1
      omega
    · exact absurd (Common.smul_basisState_apply_of_ne _ (Ne.symm hm)) hmn

/-! ## Same-type products have zero diagonal coefficients -/

/-- Two annihilation operators have zero diagonal matrix coefficient because their product carries
particle-number charge `-2`. -/
theorem matrixCoeff_annihilate_comp_annihilate (i j : Mode) (n : Occupation Mode) :
    Common.matrixCoeff ((annihilate i).comp (annihilate j)) n n = 0 :=
  Common.diagonalCoeff_eq_zero_of_carriesGradingDegree
    ((carriesParticleNumberCharge_annihilate i).comp (carriesParticleNumberCharge_annihilate j))
    (by norm_num) n

/-- Two creation operators have zero diagonal matrix coefficient because their product carries
particle-number charge `+2`. -/
theorem matrixCoeff_create_comp_create (i j : Mode) (n : Occupation Mode) :
    Common.matrixCoeff ((create i).comp (create j)) n n = 0 :=
  Common.diagonalCoeff_eq_zero_of_carriesGradingDegree
    ((carriesParticleNumberCharge_create i).comp (carriesParticleNumberCharge_create j))
    (by norm_num) n

end Fermionic
end SecondQuantization
