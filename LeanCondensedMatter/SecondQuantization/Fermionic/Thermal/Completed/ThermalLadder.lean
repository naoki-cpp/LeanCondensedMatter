import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.CanonicalAnticommutationRelations
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.Completed.GibbsLadderIntertwining

set_option linter.style.header false

/-!
# Thermal data for completed fermionic ladder operators

The completed free-Gibbs KMS bridge repeatedly needs the same two facts about a single fermionic
ladder operator:

* its bounded operator on completed Fock space intertwines with the Gibbs density operator by a
  scalar Boltzmann factor;
* its anticommutator with any other ladder operator is a scalar multiple of the identity.

This file packages creation and annihilation into one small representation-specific operator type
and exposes those two facts uniformly.  It deliberately does not define a second pairing recursion:
the resulting data are intended to feed the implementation-independent
`Common.BlochDeDominicis.ExpectationPairingRecursion` layer.
-/

namespace SecondQuantization
namespace Fermionic

open QuantumTheory

noncomputable section

variable {Mode : Type*} [LinearOrder Mode]

/-- A single bounded fermionic ladder operator in the completed representation. -/
inductive CompletedThermalLadder (Mode : Type*) where
  | create (i : Mode)
  | annihilate (i : Mode)
  deriving DecidableEq

namespace CompletedThermalLadder

/-- The bounded completed-Fock-space operator represented by a thermal ladder label. -/
noncomputable def operator : CompletedThermalLadder Mode →
    CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode
  | .create i => completedCreate i
  | .annihilate i => completedAnnihilate i

/-- The one-mode scalar appearing when the Gibbs density operator is commuted past a ladder
operator. -/
noncomputable def gibbsFactor (ε : Mode → ℝ) (β : ℝ) : CompletedThermalLadder Mode → ℂ
  | .create i => Complex.exp (-(β : ℂ) * (ε i : ℂ))
  | .annihilate i => Complex.exp ((β : ℂ) * (ε i : ℂ))

/-- The scalar anticommutator coefficient for two completed fermionic ladder operators. -/
noncomputable def anticommutatorValue :
    CompletedThermalLadder Mode → CompletedThermalLadder Mode → ℂ
  | .create _, .create _ => 0
  | .annihilate _, .annihilate _ => 0
  | .create i, .annihilate j => if i = j then 1 else 0
  | .annihilate i, .create j => if i = j then 1 else 0

@[simp]
theorem operator_create (i : Mode) :
    operator (CompletedThermalLadder.create i) = completedCreate i := rfl

@[simp]
theorem operator_annihilate (i : Mode) :
    operator (CompletedThermalLadder.annihilate i) = completedAnnihilate i := rfl

omit [LinearOrder Mode] in
@[simp]
theorem gibbsFactor_create (ε : Mode → ℝ) (β : ℝ) (i : Mode) :
    gibbsFactor ε β (CompletedThermalLadder.create i) =
      Complex.exp (-(β : ℂ) * (ε i : ℂ)) := rfl

omit [LinearOrder Mode] in
@[simp]
theorem gibbsFactor_annihilate (ε : Mode → ℝ) (β : ℝ) (i : Mode) :
    gibbsFactor ε β (CompletedThermalLadder.annihilate i) =
      Complex.exp ((β : ℂ) * (ε i : ℂ)) := rfl

/-- Uniform completed free-Gibbs intertwining for a creation or annihilation operator. -/
theorem completedFreeGibbsDensityOperator_comp_operator
    (ε : Mode → ℝ) (β : ℝ) (hsum : PurePointGibbsSummable (fermionEnergy ε) β)
    (C : CompletedThermalLadder Mode) :
    (purePointGibbsDensityOperator completedOccupationHilbertBasis
        (fermionEnergy ε) β hsum).op.comp C.operator =
      C.gibbsFactor ε β •
        (C.operator.comp
          (purePointGibbsDensityOperator completedOccupationHilbertBasis
            (fermionEnergy ε) β hsum).op) := by
  cases C with
  | create i =>
      exact completedFreeGibbsDensityOperator_comp_create ε β hsum i
  | annihilate i =>
      exact completedFreeGibbsDensityOperator_comp_annihilate ε β hsum i

/-- Uniform completed CAR: the anticommutator of any two thermal ladder operators is their scalar
coefficient times the identity. -/
theorem completedAnticomm_operator_operator
    (C D : CompletedThermalLadder Mode) :
    completedAnticomm C.operator D.operator =
      C.anticommutatorValue D •
        ContinuousLinearMap.id ℂ (CompletedFockSpace Mode) := by
  cases C with
  | create i =>
      cases D with
      | create j =>
          rw [operator_create, operator_create, completedAnticomm_create_create]
          simp [anticommutatorValue]
      | annihilate j =>
          rw [operator_create, operator_annihilate, completedAnticomm_create_annihilate]
          by_cases h : i = j <;> simp [anticommutatorValue, h]
  | annihilate i =>
      cases D with
      | create j =>
          rw [operator_annihilate, operator_create, completedAnticomm_annihilate_create]
          by_cases h : i = j <;> simp [anticommutatorValue, h]
      | annihilate j =>
          rw [operator_annihilate, operator_annihilate, completedAnticomm_annihilate_annihilate]
          simp [anticommutatorValue]

end CompletedThermalLadder

end
end Fermionic
end SecondQuantization
