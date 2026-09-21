import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.TimedField
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeGibbsDensityOperator

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

/-- Closed form after extracting the two imaginary-time exponential factors. -/
theorem timedFieldPairContraction_eq
    (ε : Mode → ℝ) (β : ℝ) (A B : TimedField Mode) :
    timedFieldPairContraction ε β A B =
      Complex.exp (((A.time * externalFieldLabelEnergyShift ε A.label : ℝ) : ℂ)) *
        Complex.exp (((B.time * externalFieldLabelEnergyShift ε B.label : ℝ) : ℂ)) *
          (freeGibbsDensityOperator ε β).expectation
            (Common.finiteHilbertOperatorAlgEquiv
              ((bareExternalFieldOperator A.label).comp
                (bareExternalFieldOperator B.label))) := by
  simp only [timedFieldPairContraction,
    freeGibbsDensityOperator_expectation_eq_finiteGibbsExpectation]
  rw [timedFieldOperator_eq_smul, timedFieldOperator_eq_smul,
    LinearMap.smul_comp, LinearMap.comp_smul, smul_smul,
    Common.finiteGibbsExpectation_smul]

end Fermionic
end SecondQuantization
