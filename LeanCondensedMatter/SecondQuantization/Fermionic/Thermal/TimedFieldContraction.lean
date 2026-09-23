import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.TimedField
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeGibbsGreenFunction

set_option linter.style.header false

/-!
# Free-Gibbs contractions of time-labelled fermionic fields

This module owns the canonical free-Gibbs contraction of two time-labelled creation or annihilation
fields. The construction is independent of any diagram representation and is shared by diagrammatic
consumers through the thermal layer.
-/

namespace SecondQuantization
namespace Fermionic

open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- Canonical free Gibbs density-state contraction of two time-labelled fermionic fields. -/
noncomputable def timedFieldPairContraction
    (ε : Mode → ℝ) (β : ℝ) (A B : TimedField Mode) : ℂ :=
  (freeGibbsDensityOperator ε β).expectation
    (Common.finiteHilbertOperatorAlgEquiv
      ((timedFieldOperator ε A).comp (timedFieldOperator ε B)))


/-- Closed form of a time-labelled pair contraction. The mixed contractions are the
Bloch–de Dominicis two-point kernels; anomalous contractions vanish. -/
theorem timedFieldPairContraction_eq
    (ε : Mode → ℝ) (β : ℝ) (A B : TimedField Mode) :
    timedFieldPairContraction ε β A B =
      Complex.exp (((A.time * externalFieldLabelEnergyShift ε A.label : ℝ) : ℂ)) *
        Complex.exp (((B.time * externalFieldLabelEnergyShift ε B.label : ℝ) : ℂ)) *
          match A.label, B.label with
          | .annihilation i, .creation j =>
              if i = j then
                Complex.exp ((β : ℂ) * (ε i : ℂ)) /
                  (Complex.exp ((β : ℂ) * (ε i : ℂ)) + 1)
              else 0
          | .creation i, .annihilation j =>
              if j = i then 1 / (Complex.exp ((β : ℂ) * (ε j : ℂ)) + 1) else 0
          | .annihilation _, .annihilation _ => 0
          | .creation _, .creation _ => 0 := by
  rw [timedFieldPairContraction, timedFieldOperator_eq_smul, timedFieldOperator_eq_smul,
    LinearMap.smul_comp, LinearMap.comp_smul, smul_smul, map_smul,
    map_smul_of_tower]
  cases A.label <;> cases B.label <;>
    simp only [bareExternalFieldOperator]
  · rw [freeGibbsDensityOperator_expectation_annihilate_comp_annihilate]
  · rw [freeGibbsDensityOperator_expectation_annihilate_comp_create]
  · rw [freeGibbsDensityOperator_expectation_create_comp_annihilate]
  · rw [freeGibbsDensityOperator_expectation_create_comp_create]

end Fermionic
end SecondQuantization
