import LeanCondensedMatter.Combinatorics.PerfectPairing.Evaluation
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.DysonDiagramExpansion.Flattening
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.Quartic.LegFamily
import LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation.DysonVertexMoment
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeBoltzmannCore
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeGibbsDensityOperator
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.TimedFieldContraction
import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteGibbsExpectationBridge
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.Induction

set_option linter.style.header false

/-!
# Dyson diagram expansion: canonical pairing evaluation

The finite Bloch--de Dominicis calculation stays local to the public Dyson-moment endpoint. Public
Dyson pairing statements are expressed through the combinatorics-owned `Pairing.evaluation` boundary
with the canonical free Gibbs density-state pair kernel.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- Canonical free Gibbs density-state contraction of two flattened quartic Dyson legs. -/
noncomputable def flatVertexLegPairValue {n : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (q : Fin n → QuarticVertexLabel Mode)
    (τ : Fin n → ℝ) (a b : Fin (2 * (2 * n))) : ℂ :=
  timedFieldPairContraction ε β
    (quarticLegFieldForSequence q τ a) (quarticLegFieldForSequence q τ b)

private theorem flatVertexLegPairValue_eq_finiteGibbsExpectation {n : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (q : Fin n → QuarticVertexLabel Mode)
    (τ : Fin n → ℝ) (a b : Fin (2 * (2 * n))) :
    flatVertexLegPairValue ε β q τ a b =
      Common.finiteGibbsExpectation (fermionEnergy ε) β
        ((quarticLegOperatorForSequence ε q τ a).comp
          (quarticLegOperatorForSequence ε q τ b)) := by
  rw [flatVertexLegPairValue, timedFieldPairContraction,
    timedFieldOperator_quarticLegFieldForSequence, timedFieldOperator_quarticLegFieldForSequence,
    freeGibbsDensityOperator_expectation_eq_finiteGibbsExpectation]

/-- Canonical scalar value of a flattened-leg pairing. -/
noncomputable def flatVertexLegPairingEvaluation {n : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (q : Fin n → QuarticVertexLabel Mode)
    (τ : Fin n → ℝ) (pairing : Pairing (2 * n)) : ℂ :=
  pairing.evaluation (pairing.weight Common.Statistics.fermion)
    (flatVertexLegPairValue ε β q τ)

/-! ## Pair-kernel regularity -/

/-- Closed form of the canonical flattened-leg pair kernel. -/
theorem flatVertexLegPairValue_eq {n : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (q : Fin n → QuarticVertexLabel Mode)
    (τ : Fin n → ℝ) (a b : Fin (2 * (2 * n))) :
    flatVertexLegPairValue ε β q τ a b =
      Complex.exp ((τ (flatVertexIndex n a) * quarticLegEnergyShiftForSequence ε q a : ℝ) : ℂ) *
        Complex.exp ((τ (flatVertexIndex n b) * quarticLegEnergyShiftForSequence ε q b : ℝ) : ℂ) *
        (freeGibbsDensityOperator ε β).expectation
          (Common.finiteHilbertOperatorAlgEquiv
            ((quarticLocalLegOperator (q (flatVertexIndex n a)) (flatLocalLeg n a)).comp
              (quarticLocalLegOperator (q (flatVertexIndex n b)) (flatLocalLeg n b)))) := by
  rw [flatVertexLegPairValue_eq_finiteGibbsExpectation,
    quarticLegOperatorForSequence_eq_smul, quarticLegOperatorForSequence_eq_smul,
    LinearMap.smul_comp, LinearMap.comp_smul, smul_smul,
    Common.finiteGibbsExpectation_smul,
    ← freeGibbsDensityOperator_expectation_eq_finiteGibbsExpectation]

/-- Canonical pairing evaluation is continuous in the vertex-time assignment. -/
theorem continuous_flatVertexLegPairingEvaluation {n : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (q : Fin n → QuarticVertexLabel Mode)
    (pairing : Pairing (2 * n)) :
    Continuous (fun τ : Fin n → ℝ => flatVertexLegPairingEvaluation ε β q τ pairing) := by
  simp only [flatVertexLegPairingEvaluation, Combinatorics.Pairing.evaluation]
  exact continuous_const.mul (continuous_finsetProd _ fun pr _ => by
    simp only [flatVertexLegPairValue_eq]
    fun_prop)

/-! ## Integrating the pairing sum over the ordered simplex -/

/-- `dysonVertexMoment` of the quartic interaction in the canonical pairing-evaluator presentation. -/
theorem dysonVertexMoment_quarticInteraction_eq_sum_vertexLabel_pairingEvaluation {α : Type*}
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ) (S : Finset α) :
    dysonVertexMoment ε β (quarticInteraction g) S =
      (S.card.factorial : ℂ) * (-1 : ℂ) ^ S.card *
        ∑ q : Fin S.card → QuarticVertexLabel Mode, (∏ i, g (q i)) *
          ∑ pairing : Pairing (2 * S.card),
            intervalIntegral.orderedSimplexIntegral S.card β
              (fun τ => flatVertexLegPairingEvaluation ε β q τ pairing) := by
  classical
  have hkey :=
    freeGibbsDensityOperator_expectation_comp_dysonCoeff_quarticInteraction
      ε β g S.card β LinearMap.id
  simp only [LinearMap.id_comp] at hkey
  have hsum :
      ∑ q : Fin S.card → QuarticVertexLabel Mode, (∏ i, g (q i)) *
        intervalIntegral.orderedSimplexIntegral S.card β
          (fun τ => (freeGibbsDensityOperator ε β).expectation
            (Common.finiteHilbertOperatorAlgEquiv
              (nestedVertexOperatorComp ε S.card q τ))) =
      ∑ q : Fin S.card → QuarticVertexLabel Mode, (∏ i, g (q i)) *
        ∑ pairing : Pairing (2 * S.card),
          intervalIntegral.orderedSimplexIntegral S.card β
            (fun τ => flatVertexLegPairingEvaluation ε β q τ pairing) :=
    Finset.sum_congr rfl fun q _ => by
      have hpoint (τ : Fin S.card → ℝ) :
          (freeGibbsDensityOperator ε β).expectation
              (Common.finiteHilbertOperatorAlgEquiv (nestedVertexOperatorComp ε S.card q τ)) =
            ∑ pairing : Pairing (2 * S.card),
              flatVertexLegPairingEvaluation ε β q τ pairing := by
        rw [freeGibbsDensityOperator_expectation_eq_finiteGibbsExpectation,
          ← prod_ofFn_quarticLegOperatorForSequence_eq_nestedVertexOperatorComp]
        have hgen :=
          Common.BlochDeDominicis.finiteGibbsExpectation_prod_eq_sum_pairing
            Common.Statistics.fermion (fermionEnergy ε) β (2 * S.card)
            (quarticLegOperatorForSequence ε q τ) (quarticLegEnergyShiftForSequence ε q)
            (flatVertexLegCommutatorCoeff ε q τ)
            (fun p => by
              rw [← timedFieldOperator_quarticLegFieldForSequence ε q τ p]
              simpa [quarticLegFieldForSequence, quarticLegEnergyShiftForSequence,
                quarticLocalLegEnergyShift, Common.flatVertexIndex, Common.flatLocalLeg] using
                (heisenbergEvolve_timedFieldOperator ε β
                  (quarticLegFieldForSequence q τ p)))
            (fun i j _ => zetaCommutator_quarticLegOperatorForSequence ε q τ i j)
            (fun i => one_sub_zetaInt_fermion_mul_exp_ne_zero
              (quarticLegEnergyShiftForSequence ε q i) β)
        simpa only [flatVertexLegPairingEvaluation, Combinatorics.Pairing.evaluation,
          flatVertexLegPairValue_eq_finiteGibbsExpectation] using hgen
      rw [intervalIntegral.orderedSimplexIntegral_congr hpoint,
        intervalIntegral.orderedSimplexIntegral_finsetSum _ S.card β _
          (fun pairing _ => continuous_flatVertexLegPairingEvaluation ε β q pairing)]
  rw [dysonVertexMoment_eq_freeGibbsDensityOperator_expectation, hkey, mul_assoc, hsum]

end Fermionic
end SecondQuantization
