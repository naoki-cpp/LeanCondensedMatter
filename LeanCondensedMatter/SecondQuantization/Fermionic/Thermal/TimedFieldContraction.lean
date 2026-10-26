import LeanCondensedMatter.Combinatorics.PerfectPairing.Evaluation
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.TimedField
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeBoltzmannCore
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.GibbsExpectation.Recursion
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
    Common.finiteGibbsExpectation, map_smul, smul_eq_mul]
  rfl

/-- Grand-canonical finite free-fermion Wick expansion for physical-time fields.
The time evolution uses `ε`, while the Gibbs distribution and KMS rotation use `ε - μ`.
This is not a fixed-particle-number canonical Wick theorem. -/
theorem grandCanonicalGibbsExpectation_prod_timedFieldOperator_eq_sum_pairing
    (ε : Mode → ℝ) (β μ : ℝ) (n : ℕ) (fields : Fin (2 * n) → TimedField Mode) :
    Common.finiteGibbsExpectation (fermionEnergy (fun i => ε i - μ)) β
        (List.prod (List.ofFn (fun p => timedFieldOperator ε (fields p)))) =
      ∑ pairing : Pairing n,
        pairing.evaluation (pairing.weight Common.Statistics.fermion)
          (fun a b => Common.finiteGibbsExpectation (fermionEnergy (fun i => ε i - μ)) β
            ((timedFieldOperator ε (fields a)).comp
              (timedFieldOperator ε (fields b)))) := by
  have hgen :=
    Common.BlochDeDominicis.finiteGibbsExpectation_prod_eq_sum_pairing
      Common.Statistics.fermion (fermionEnergy (fun i => ε i - μ)) β n
      (fun p => timedFieldOperator ε (fields p))
      (fun p => externalFieldLabelEnergyShift (fun i => ε i - μ) (fields p).label)
      (fun a b => timedFieldCommutatorCoeff ε (fields a) (fields b))
      (fun p => heisenbergEvolve_timedFieldOperator ε (fun i => ε i - μ) β (fields p))
      (fun a b _ => zetaCommutator_timedFieldOperator ε (fields a) (fields b))
      (fun p => one_sub_zetaInt_fermion_mul_exp_ne_zero
        (externalFieldLabelEnergyShift (fun i => ε i - μ) (fields p).label) β)
  simpa only [Combinatorics.Pairing.evaluation] using hgen

end Fermionic
end SecondQuantization
