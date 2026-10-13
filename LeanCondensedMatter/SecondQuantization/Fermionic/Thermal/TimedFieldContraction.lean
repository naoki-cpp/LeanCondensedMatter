import LeanCondensedMatter.Combinatorics.PerfectPairing.Evaluation
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.TimedField
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeBoltzmannCore
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.Induction
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

open Combinatorics
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

/-- Finite-temperature Wick (Bloch--de Dominicis) expansion for an arbitrary even family of
time-labelled free fermionic fields. The free Gibbs state and the canonical two-field
contractions are independent of any Dyson or diagrammatic ordering. -/
theorem freeGibbsDensityOperator_expectation_prod_timedFieldOperator_eq_sum_pairing
    (ε : Mode → ℝ) (β : ℝ) (n : ℕ) (fields : Fin (2 * n) → TimedField Mode) :
    (freeGibbsDensityOperator ε β).expectation
        (Common.finiteHilbertOperatorAlgEquiv
          (List.prod (List.ofFn (fun p => timedFieldOperator ε (fields p))))) =
      ∑ pairing : Pairing n,
        pairing.evaluation (pairing.weight Common.Statistics.fermion)
          (fun a b => timedFieldPairContraction ε β (fields a) (fields b)) := by
  have hgen :=
    Common.BlochDeDominicis.finiteGibbsExpectation_prod_eq_sum_pairing
      Common.Statistics.fermion (fermionEnergy ε) β n
      (fun p => timedFieldOperator ε (fields p))
      (fun p => externalFieldLabelEnergyShift ε (fields p).label)
      (fun a b => timedFieldCommutatorCoeff ε (fields a) (fields b))
      (fun p => heisenbergEvolve_timedFieldOperator ε β (fields p))
      (fun a b _ => zetaCommutator_timedFieldOperator ε (fields a) (fields b))
      (fun p => one_sub_zetaInt_fermion_mul_exp_ne_zero
        (externalFieldLabelEnergyShift ε (fields p).label) β)
  rw [freeGibbsDensityOperator_expectation_eq_finiteGibbsExpectation]
  simpa only [Combinatorics.Pairing.evaluation, timedFieldPairContraction,
    freeGibbsDensityOperator_expectation_eq_finiteGibbsExpectation] using hgen

end Fermionic
end SecondQuantization
