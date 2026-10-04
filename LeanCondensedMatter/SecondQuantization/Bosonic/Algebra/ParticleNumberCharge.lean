import LeanCondensedMatter.SecondQuantization.Bosonic.Algebra.CreationAnnihilation
import LeanCondensedMatter.SecondQuantization.Common.Algebra.SupportShift

set_option linter.style.header false

/-!
# Bosonic creation/annihilation operators carry particle-number charge `±1`

The bosonic mirror of `Fermionic/Algebra/ParticleNumberCharge.lean`: instantiates
`Common.CarriesShift` for `annihilate i`/`create i`, with `particleNumber` (cast to `ℤ`) as the
additive grading. The proof needs no positivity fact about the `√n`/`√(n+1)` normalization
coefficients — `Common.grading_eq_of_matrixCoeff_ne_zero_of_basisState_smul` packages the support-selection
argument, leaving only the occupation update and particle-number difference in these proofs.
-/

namespace SecondQuantization
namespace Bosonic

variable {Mode : Type*}

/-- **`annihilate i` carries particle-number charge `-1`**: it only ever connects a basis state
`m` to a basis state `n` with one fewer particle. -/
theorem carriesParticleNumberCharge_annihilate (i : Mode) :
    Common.CarriesShift
      (fun n : Occupation Mode => (particleNumber n : ℤ)) (annihilate i) (-1) := by
  classical
  intro m n hmn
  change annihilate i (basisState n) m ≠ 0 at hmn
  by_cases hi : n i = 0
  · rw [annihilate_basisState_of_zero hi] at hmn
    simp at hmn
  · apply Common.grading_eq_of_matrixCoeff_ne_zero_of_basisState_smul
      (annihilate_basisState_of_pos hi) hmn
    have hcard := particleNumber_removeOccupation_of_pos hi
    change (particleNumber (removeOccupation i n) : ℤ) = (particleNumber n : ℤ) + (-1)
    omega

/-- **`create i` carries particle-number charge `+1`**: it only ever connects a basis state `m` to
a basis state `n` with one more particle. -/
theorem carriesParticleNumberCharge_create (i : Mode) :
    Common.CarriesShift
      (fun n : Occupation Mode => (particleNumber n : ℤ)) (create i) 1 := by
  classical
  intro m n hmn
  change create i (basisState n) m ≠ 0 at hmn
  apply Common.grading_eq_of_matrixCoeff_ne_zero_of_basisState_smul
    (create_basisState_eq i n) hmn
  have hcard := particleNumber_createOccupation i n
  change (particleNumber (createOccupation i n) : ℤ) = (particleNumber n : ℤ) + 1
  omega

/-- Two annihilation operators have zero diagonal matrix coefficient. -/
theorem matrixCoeff_annihilate_comp_annihilate (i j : Mode) (n : Occupation Mode) :
    Common.matrixCoeff ((annihilate i).comp (annihilate j)) n n = 0 :=
  Common.diagonalCoeff_eq_zero_of_carriesShift
    ((carriesParticleNumberCharge_annihilate i).comp (carriesParticleNumberCharge_annihilate j))
    (by norm_num) n

/-- Two creation operators have zero diagonal matrix coefficient. -/
theorem matrixCoeff_create_comp_create (i j : Mode) (n : Occupation Mode) :
    Common.matrixCoeff ((create i).comp (create j)) n n = 0 :=
  Common.diagonalCoeff_eq_zero_of_carriesShift
    ((carriesParticleNumberCharge_create i).comp (carriesParticleNumberCharge_create j))
    (by norm_num) n

end Bosonic
end SecondQuantization
