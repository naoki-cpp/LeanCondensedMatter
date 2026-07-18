import LeanCondensedMatter.SecondQuantization.Fermionic.CreationAnnihilation
import LeanCondensedMatter.SecondQuantization.Common.ParticleNumberSelectionRule

set_option linter.style.header false

/-!
# Fermionic creation/annihilation operators carry particle-number charge `±1`

Instantiates `Common.CarriesGradingDegree` (`Common/ParticleNumberSelectionRule.lean`) for
`annihilate i`/`create i`, with grading `fermionParticleNumber` (cast to `ℤ`): `annihilate i`
carries charge `-1`, `create i` carries charge `+1`. Combined with
`Common.CarriesGradingDegree.comp` and `Common.diagonalCoeff_eq_zero_of_carriesGradingDegree`,
this reduces the same-type contraction vanishing proved by hand in `ThermalContraction.lean` to
the general particle-number selection rule.
-/

namespace SecondQuantization

variable {Mode : Type*} [DecidableEq Mode] [LinearOrder Mode]

/-- **`annihilate i` carries particle-number charge `-1`**: it only ever connects a basis state
`m` to a basis state `n` with one fewer particle, `fermionParticleNumber m = fermionParticleNumber
n - 1`. -/
theorem carriesParticleNumberCharge_annihilate (i : Mode) :
    Common.CarriesGradingDegree
      (fun n : FermionOccupation Mode => (fermionParticleNumber n : ℤ)) (annihilate i) (-1) := by
  intro m n hmn
  change annihilate i (basisState n) m ≠ 0 at hmn
  by_cases hi : i ∈ n
  · rw [annihilate_basisState_of_mem hi] at hmn
    by_cases hm : m = removeOccupation i n
    · have hcard := fermionParticleNumber_removeOccupation_of_mem hi
      rw [hm]
      change (fermionParticleNumber (removeOccupation i n) : ℤ) =
        (fermionParticleNumber n : ℤ) + (-1)
      omega
    · exact absurd (Common.smul_basisState_apply_of_ne _ (Ne.symm hm)) hmn
  · rw [annihilate_basisState_of_not_mem hi] at hmn
    simp at hmn

/-- **`create i` carries particle-number charge `+1`**: it only ever connects a basis state `m` to
a basis state `n` with one more particle, `fermionParticleNumber m = fermionParticleNumber n +
1`. -/
theorem carriesParticleNumberCharge_create (i : Mode) :
    Common.CarriesGradingDegree
      (fun n : FermionOccupation Mode => (fermionParticleNumber n : ℤ)) (create i) 1 := by
  intro m n hmn
  change create i (basisState n) m ≠ 0 at hmn
  by_cases hi : i ∈ n
  · rw [create_basisState_of_mem hi] at hmn
    simp at hmn
  · rw [create_basisState_of_not_mem hi] at hmn
    by_cases hm : m = insertOccupation i n
    · have hcard := fermionParticleNumber_insertOccupation_of_not_mem hi
      rw [hm]
      change (fermionParticleNumber (insertOccupation i n) : ℤ) =
        (fermionParticleNumber n : ℤ) + 1
      omega
    · exact absurd (Common.smul_basisState_apply_of_ne _ (Ne.symm hm)) hmn

end SecondQuantization
