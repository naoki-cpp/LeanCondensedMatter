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
  refine Common.CarriesShift.of_basisState_smul
    (target := removeOccupation i)
    (coeff := fun n : Occupation Mode => (Real.sqrt (n i : ℝ) : ℂ))
    (annihilate_basisState_eq i) ?_
  intro n hn
  have hi : n i ≠ 0 := by
    intro h
    simp [h] at hn
  have hcard := particleNumber_removeOccupation_of_pos hi
  change (particleNumber (removeOccupation i n) : ℤ) =
    (particleNumber n : ℤ) + (-1)
  omega

/-- **`create i` carries particle-number charge `+1`**: it only ever connects a basis state `m` to
a basis state `n` with one more particle. -/
theorem carriesParticleNumberCharge_create (i : Mode) :
    Common.CarriesShift
      (fun n : Occupation Mode => (particleNumber n : ℤ)) (create i) 1 := by
  refine Common.CarriesShift.of_basisState_smul
    (target := createOccupation i)
    (coeff := fun n : Occupation Mode => (Real.sqrt (n i + 1 : ℝ) : ℂ))
    (create_basisState_eq i) ?_
  intro n _
  have hcard := particleNumber_createOccupation i n
  change (particleNumber (createOccupation i n) : ℤ) =
    (particleNumber n : ℤ) + 1
  omega

end Bosonic
end SecondQuantization
