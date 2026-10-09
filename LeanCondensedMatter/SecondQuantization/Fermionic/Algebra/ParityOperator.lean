import LeanCondensedMatter.SecondQuantization.Common.Algebra.ParityOperator
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.ParticleNumberCharge

set_option linter.style.header false

/-!
# Fermion-number parity

The diagonal involution on occupation Fock space realizes `(-1)^N`.
Its conjugation action follows from the support-shift characterization.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode]

/-- The fermion-number parity involution on algebraic occupation Fock space. -/
noncomputable def fermionParityOperator :
    OccupationFock Mode →ₗ[ℂ] OccupationFock Mode :=
  Common.parityOperator
    (fun n : Occupation Mode => ((particleNumber n : ℤ) : ZMod 2))

/-- The occupation basis action is multiplication by `(-1)^N`. -/
theorem fermionParityOperator_basisState (n : Occupation Mode) :
    fermionParityOperator (basisState n) =
      (-1 : ℂ) ^ particleNumber n • basisState n := by
  change Common.parityOperator
      (fun n : Occupation Mode => ((particleNumber n : ℤ) : ZMod 2))
      (Common.basisState n) = _
  rw [Common.parityOperator_basisState]
  congr 1
  simpa only [Int.cast_natCast] using
    (Common.parityEigenvalue_nat (particleNumber n))

theorem fermionParityOperator_comp_self :
    (fermionParityOperator (Mode := Mode)).comp fermionParityOperator =
      (LinearMap.id : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) :=
  Common.parityOperator_comp_self _

end Fermionic
end SecondQuantization
