import LeanCondensedMatter.SecondQuantization.Bosonic.Algebra.CreationAnnihilation
import LeanCondensedMatter.SecondQuantization.Common.Algebra.ParticleNumberSelectionRule

set_option linter.style.header false

/-!
# Bosonic creation/annihilation operators carry particle-number charge `±1`

The bosonic mirror of `Fermionic/Algebra/ParticleNumberCharge.lean`: instantiates
`Common.CarriesGradingDegree` (`Common/Algebra/ParticleNumberSelectionRule.lean`) for `annihilate
i`/`create i`, with grading `particleNumber` (cast to `ℤ`). The proof needs no positivity fact
about the `√n`/`√(n+1)` normalization coefficients — `Common.smul_basisState_apply_of_ne` kills
the off-target basis coefficient for *any* scalar multiplier, so acting with `annihilate i`/
`create i` on `basisState n` has a nonzero `m`-coefficient only when `m` is exactly the one basis
state (`removeOccupation i n`/`createOccupation i n`) the operator's basis-level action targets.
This confirms the claim already made in `Fermionic/Thermal/WeightedContraction.lean`'s module docstring
that the particle-number selection rule is a `U(1)` fact independent of exchange statistics:
nothing here uses that modes commute rather than anticommute.
-/

namespace SecondQuantization
namespace Bosonic

variable {Mode : Type*} [DecidableEq Mode]

/-- **`annihilate i` carries particle-number charge `-1`**: it only ever connects a basis state
`m` to a basis state `n` with one fewer particle. -/
theorem carriesParticleNumberCharge_annihilate (i : Mode) :
    Common.CarriesGradingDegree
      (fun n : Occupation Mode => (particleNumber n : ℤ)) (annihilate i) (-1) := by
  intro m n hmn
  change annihilate i (basisState n) m ≠ 0 at hmn
  by_cases hi : n i = 0
  · rw [annihilate_basisState_of_zero hi] at hmn
    simp at hmn
  · rw [annihilate_basisState_of_pos hi] at hmn
    by_cases hm : m = removeOccupation i n
    · have hcard := particleNumber_removeOccupation_of_pos hi
      rw [hm]
      change (particleNumber (removeOccupation i n) : ℤ) = (particleNumber n : ℤ) + (-1)
      omega
    · exact absurd (Common.smul_basisState_apply_of_ne _ (Ne.symm hm)) hmn

/-- **`create i` carries particle-number charge `+1`**: it only ever connects a basis state `m` to
a basis state `n` with one more particle. -/
theorem carriesParticleNumberCharge_create (i : Mode) :
    Common.CarriesGradingDegree
      (fun n : Occupation Mode => (particleNumber n : ℤ)) (create i) 1 := by
  intro m n hmn
  change create i (basisState n) m ≠ 0 at hmn
  rw [create_basisState_eq] at hmn
  by_cases hm : m = createOccupation i n
  · have hcard := particleNumber_createOccupation i n
    rw [hm]
    change (particleNumber (createOccupation i n) : ℤ) = (particleNumber n : ℤ) + 1
    omega
  · exact absurd (Common.smul_basisState_apply_of_ne _ (Ne.symm hm)) hmn

/-- Two annihilation operators have zero diagonal matrix coefficient. -/
theorem matrixCoeff_annihilate_comp_annihilate (i j : Mode) (n : Occupation Mode) :
    Common.matrixCoeff ((annihilate i).comp (annihilate j)) n n = 0 :=
  Common.diagonalCoeff_eq_zero_of_carriesGradingDegree
    ((carriesParticleNumberCharge_annihilate i).comp (carriesParticleNumberCharge_annihilate j))
    (by norm_num) n

/-- Two creation operators have zero diagonal matrix coefficient. -/
theorem matrixCoeff_create_comp_create (i j : Mode) (n : Occupation Mode) :
    Common.matrixCoeff ((create i).comp (create j)) n n = 0 :=
  Common.diagonalCoeff_eq_zero_of_carriesGradingDegree
    ((carriesParticleNumberCharge_create i).comp (carriesParticleNumberCharge_create j))
    (by norm_num) n

end Bosonic
end SecondQuantization
