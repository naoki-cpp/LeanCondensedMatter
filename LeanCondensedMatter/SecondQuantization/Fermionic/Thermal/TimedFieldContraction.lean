import LeanCondensedMatter.Combinatorics.PerfectPairing.Evaluation
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.TimedField
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeBoltzmannCore
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.GibbsExpectation.Recursion

set_option linter.style.header false

/-!
# Free-Gibbs contractions of time-labelled fermionic fields

This module owns the grand-canonical contraction of time-labelled free fermionic fields.
Physical evolution uses ε; thermal occupation weights use ε - μ. Diagrammatic clients that
retain zero chemical potential specialize μ = 0 explicitly.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- Grand-canonical two-point contraction with physical-time fields at ε and Gibbs weights
at ε - μ. -/
noncomputable def grandCanonicalTimedFieldPairContraction
    (ε : Mode → ℝ) (β μ : ℝ) (A B : TimedField Mode) : ℂ :=
  Common.finiteGibbsExpectation (fermionEnergy (fun i => ε i - μ)) β
    ((timedFieldOperator ε A).comp (timedFieldOperator ε B))

/-- Factor physical imaginary-time evolution from an explicit-μ Gibbs pair contraction. -/
theorem grandCanonicalTimedFieldPairContraction_eq
    (ε : Mode → ℝ) (β μ : ℝ) (A B : TimedField Mode) :
    grandCanonicalTimedFieldPairContraction ε β μ A B =
      Complex.exp (((A.time * externalFieldLabelEnergyShift ε A.label : ℝ) : ℂ)) *
        Complex.exp (((B.time * externalFieldLabelEnergyShift ε B.label : ℝ) : ℂ)) *
          Common.finiteGibbsExpectation (fermionEnergy (fun i => ε i - μ)) β
            ((bareExternalFieldOperator A.label).comp
              (bareExternalFieldOperator B.label)) := by
  simp only [grandCanonicalTimedFieldPairContraction]
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
