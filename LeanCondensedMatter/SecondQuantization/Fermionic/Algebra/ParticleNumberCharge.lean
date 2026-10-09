import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.CreationAnnihilation
import LeanCondensedMatter.SecondQuantization.Common.Algebra.SupportShift
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.NumberOperator
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.QuarticInteraction
import Mathlib.Data.ZMod.Basic

set_option linter.style.header false

/-!
# Fermionic particle-number charge

This module instantiates `Common.CarriesShift` for fermionic creation and annihilation operators,
with the occupation particle number as an integer-valued grading. An annihilation operator carries
shift `-1`, while a creation operator carries shift `+1`.

As an algebraic consequence, products of two annihilation operators or two creation operators carry
nonzero shift and therefore have vanishing diagonal occupation-basis coefficients. Thermal modules
may lift these basis-level statements to weighted traces and time-ordered correlators.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode]

/-- **`annihilate i` carries particle-number charge `-1`**: it only ever connects a basis state
`m` to a basis state `n` with one fewer particle, `particleNumber m = particleNumber
n - 1`. -/
theorem carriesParticleNumberCharge_annihilate (i : Mode) :
    Common.CarriesShift
      (fun n : Occupation Mode => (particleNumber n : ℤ)) (annihilate i) (-1) := by
  intro m n hmn
  change annihilate i (basisState n) m ≠ 0 at hmn
  by_cases hi : i ∈ n
  · apply Common.grading_eq_of_matrixCoeff_ne_zero_of_basisState_smul
      (annihilate_basisState_of_mem hi) hmn
    have hcard := particleNumber_removeOccupation_of_mem hi
    change (particleNumber (removeOccupation i n) : ℤ) =
      (particleNumber n : ℤ) + (-1)
    omega
  · rw [annihilate_basisState_of_not_mem hi] at hmn
    simp at hmn

/-- **`create i` carries particle-number charge `+1`**: it only ever connects a basis state `m` to
a basis state `n` with one more particle, `particleNumber m = particleNumber n +
1`. -/
theorem carriesParticleNumberCharge_create (i : Mode) :
    Common.CarriesShift
      (fun n : Occupation Mode => (particleNumber n : ℤ)) (create i) 1 := by
  intro m n hmn
  change create i (basisState n) m ≠ 0 at hmn
  by_cases hi : i ∈ n
  · rw [create_basisState_of_mem hi] at hmn
    simp at hmn
  · apply Common.grading_eq_of_matrixCoeff_ne_zero_of_basisState_smul
      (create_basisState_of_not_mem hi) hmn
    have hcard := particleNumber_insertOccupation_of_not_mem hi
    change (particleNumber (insertOccupation i n) : ℤ) =
      (particleNumber n : ℤ) + 1
    omega

/-! ## Composite operators and fermion parity -/

/-- A number operator preserves total particle number. -/
theorem carriesParticleNumberCharge_numberOperator (i : Mode) :
    Common.CarriesShift
      (fun n : Occupation Mode => (particleNumber n : ℤ)) (numberOperator i) 0 := by
  simpa [numberOperator] using
    (carriesParticleNumberCharge_create i).comp
      (carriesParticleNumberCharge_annihilate i)

/-- A number-conserving quartic vertex has zero particle-number shift. -/
theorem carriesParticleNumberCharge_quarticVertexOperator (q : Common.QuarticVertexLabel Mode) :
    Common.CarriesShift (fun n : Occupation Mode => (particleNumber n : ℤ))
      (quarticVertexOperator q) 0 := by
  have h :=
    (carriesParticleNumberCharge_create q.create₁).comp
      ((carriesParticleNumberCharge_create q.create₂).comp
        ((carriesParticleNumberCharge_annihilate q.annihilate₂).comp
          (carriesParticleNumberCharge_annihilate q.annihilate₁)))
  simpa [quarticVertexOperator, Common.quarticVertexOperator] using h

/-- A finite, number-conserving quartic interaction also preserves particle number. -/
theorem carriesParticleNumberCharge_quarticInteractionOn
    (support : Finset (Common.QuarticVertexLabel Mode))
    (g : Common.QuarticVertexLabel Mode → ℂ) :
    Common.CarriesShift (fun n : Occupation Mode => (particleNumber n : ℤ))
      (quarticInteractionOn support g) 0 := by
  change Common.CarriesShift (fun n : Occupation Mode => (particleNumber n : ℤ))
    (∑ q ∈ support, g q • quarticVertexOperator q) 0
  apply Common.CarriesShift.sum
  intro q hq
  exact (carriesParticleNumberCharge_quarticVertexOperator q).smul (g q)

/-- A sum of one creation and one annihilation operator has fermion parity one,
although its two summands carry opposite integer particle-number shifts. -/
theorem carriesFermionParity_create_add_annihilate (i : Mode) :
    Common.CarriesShift
      (fun n : Occupation Mode => ((particleNumber n : ℤ) : ZMod 2))
      (create i + annihilate i) 1 := by
  have hcreate : Common.CarriesShift
      (fun n : Occupation Mode => ((particleNumber n : ℤ) : ZMod 2))
      (create i) 1 := by
    simpa using
      (carriesParticleNumberCharge_create i).map (Int.castAddHom (ZMod 2))
  have hannihilate : Common.CarriesShift
      (fun n : Occupation Mode => ((particleNumber n : ℤ) : ZMod 2))
      (annihilate i) 1 := by
    have hneg : ((-1 : ℤ) : ZMod 2) = 1 := by decide
    simpa [hneg] using
      (carriesParticleNumberCharge_annihilate i).map (Int.castAddHom (ZMod 2))
  exact hcreate.add hannihilate

/-! ## Same-type products have zero diagonal coefficients -/

/-- Two annihilation operators have zero diagonal matrix coefficient because their product carries
particle-number charge `-2`. -/
theorem matrixCoeff_annihilate_comp_annihilate (i j : Mode) (n : Occupation Mode) :
    Common.matrixCoeff ((annihilate i).comp (annihilate j)) n n = 0 :=
  Common.diagonalCoeff_eq_zero_of_carriesShift
    ((carriesParticleNumberCharge_annihilate i).comp (carriesParticleNumberCharge_annihilate j))
    (by norm_num) n

/-- Two creation operators have zero diagonal matrix coefficient because their product carries
particle-number charge `+2`. -/
theorem matrixCoeff_create_comp_create (i j : Mode) (n : Occupation Mode) :
    Common.matrixCoeff ((create i).comp (create j)) n n = 0 :=
  Common.diagonalCoeff_eq_zero_of_carriesShift
    ((carriesParticleNumberCharge_create i).comp (carriesParticleNumberCharge_create j))
    (by norm_num) n

end Fermionic
end SecondQuantization
