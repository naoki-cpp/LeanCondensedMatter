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

/-- Number operators preserve fermion parity. -/
theorem fermionParityOperator_conjugate_numberOperator (i : Mode) :
    (fermionParityOperator (Mode := Mode)).comp
        ((numberOperator i).comp fermionParityOperator) = numberOperator i := by
  have hshift : Common.CarriesShift
      (fun n : Occupation Mode => ((particleNumber n : ℤ) : ZMod 2))
      (numberOperator i) 0 := by
    simpa [Function.comp_def] using
      (carriesParticleNumberCharge_numberOperator i).map (Int.castAddHom (ZMod 2))
  have h := (Common.carriesShift_iff_parityOperator_conjugate
    (fun n : Occupation Mode => ((particleNumber n : ℤ) : ZMod 2))
    (numberOperator i) 0).mp hshift
  simpa [fermionParityOperator] using h

/-- A finite number-conserving quartic interaction preserves fermion parity. -/
theorem fermionParityOperator_conjugate_quarticInteractionOn
    (support : Finset (Common.QuarticVertexLabel Mode))
    (g : Common.QuarticVertexLabel Mode → ℂ) :
    (fermionParityOperator (Mode := Mode)).comp
        ((quarticInteractionOn support g).comp fermionParityOperator) =
      quarticInteractionOn support g := by
  have hshift : Common.CarriesShift
      (fun n : Occupation Mode => ((particleNumber n : ℤ) : ZMod 2))
      (quarticInteractionOn support g) 0 := by
    simpa [Function.comp_def] using
      (carriesParticleNumberCharge_quarticInteractionOn support g).map
        (Int.castAddHom (ZMod 2))
  have h := (Common.carriesShift_iff_parityOperator_conjugate
    (fun n : Occupation Mode => ((particleNumber n : ℤ) : ZMod 2))
    (quarticInteractionOn support g) 0).mp hshift
  simpa [fermionParityOperator] using h

/-- A sum of a creation and an annihilation operator is odd under parity. -/
theorem fermionParityOperator_conjugate_create_add_annihilate (i : Mode) :
    (fermionParityOperator (Mode := Mode)).comp
        ((create i + annihilate i).comp fermionParityOperator) =
      -(create i + annihilate i) := by
  have h := (Common.carriesShift_iff_parityOperator_conjugate
    (fun n : Occupation Mode => ((particleNumber n : ℤ) : ZMod 2))
    (create i + annihilate i) 1).mp
      (carriesFermionParity_create_add_annihilate i)
  simpa [fermionParityOperator] using h

end Fermionic
end SecondQuantization
