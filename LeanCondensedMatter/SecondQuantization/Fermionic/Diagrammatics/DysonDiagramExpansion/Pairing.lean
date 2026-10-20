import LeanCondensedMatter.Combinatorics.PerfectPairing.Evaluation
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.DysonDiagramExpansion.Core
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.Quartic
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.Quartic.LegFamily
import LeanCondensedMatter.Analysis.PowerSeries.Moment
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.DysonTraceSeries
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeGibbsDensityOperator
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.TimedFieldContraction
import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteGibbsExpectationBridge

set_option linter.style.header false

/-!
# Dyson diagram expansion: canonical pairing evaluation

The fermionic operator-flattening identity is a proof-local step of the Dyson-moment endpoint.
Public Dyson pairing statements use the combinatorics-owned `Pairing.evaluation` boundary with
the canonical free Gibbs density-state pair kernel.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Common

variable {Mode : Type*} [LinearOrder Mode]

/-! ## Quartic-vertex flattening used by the pairing proof -/

/-- The ordered product of the flattened evolved quartic legs is exactly the Common
interaction-picture quartic-vertex sequence. The row-major `4n` product decomposition is owned by
`Common.prod_orderedQuarticLegFamily_eq_vertexProducts`; this theorem supplies only the fermionic
imaginary-time specialization. -/
private theorem prod_ofFn_quarticLegOperatorForSequence_eq_quarticVertexSequenceInteractionPicture
    (ε : Mode → ℝ) :
    ∀ (n : ℕ) (q : Fin n → QuarticVertexLabel Mode) (τ : Fin n → ℝ),
      List.prod (List.ofFn (quarticLegOperatorForSequence ε q τ)) =
        Common.quarticVertexSequenceInteractionPicture (fermionEnergy ε) create annihilate n q τ := by
  intro n q τ
  change
    (List.ofFn (Common.orderedQuarticLegFamily
      (fun i : Fin n => fun l : Fin 4 =>
        Common.heisenbergEvolve (fermionEnergy ε) (τ i)
          (Common.quarticLocalLegOperator create annihilate (q i) l)))).prod =
      (List.ofFn (fun i : Fin n =>
        Common.heisenbergEvolve (fermionEnergy ε) (τ i)
          (Common.quarticVertexOperator create annihilate (q i)))).prod
  rw [Common.prod_orderedQuarticLegFamily_eq_vertexProducts]
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext i
  exact (Common.heisenbergEvolve_quarticVertexOperator_eq_prod
    (fermionEnergy ε) create annihilate (q i) (τ i)).symm

variable [Fintype Mode]

/-- Canonical free Gibbs density-state contraction of two flattened quartic Dyson legs. -/
noncomputable def flatVertexLegPairValue {n : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (q : Fin n → QuarticVertexLabel Mode)
    (τ : Fin n → ℝ) (a b : Fin (2 * (2 * n))) : ℂ :=
  timedFieldPairContraction ε β
    (quarticLegFieldForSequence q τ a) (quarticLegFieldForSequence q τ b)

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
  simpa [flatVertexLegPairValue, timedFieldPairContraction_eq,
    quarticLegFieldForSequence, quarticLegEnergyShiftForSequence,
    quarticLocalLegEnergyShift, quarticLocalLegOperator,
    Common.quarticLocalLegOperator, Common.flatVertexIndex, Common.flatLocalLeg]

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

/-- The generic normalized Dyson-series moment of the quartic interaction in the pairing-evaluator presentation. -/
theorem dysonVertexMoment_quarticInteraction_eq_sum_vertexLabel_pairingEvaluation {α : Type*}
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ) (S : Finset α) :
    Combinatorics.powerSeriesMomentCoeff
      (PowerSeries.normalizeByConstantCoeff
        (Common.dysonTraceSeries (fermionEnergy ε) β (quarticInteraction g))) S.card =
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
              (Common.quarticVertexSequenceInteractionPicture (fermionEnergy ε) create annihilate S.card q τ))) =
      ∑ q : Fin S.card → QuarticVertexLabel Mode, (∏ i, g (q i)) *
        ∑ pairing : Pairing (2 * S.card),
          intervalIntegral.orderedSimplexIntegral S.card β
            (fun τ => flatVertexLegPairingEvaluation ε β q τ pairing) :=
    Finset.sum_congr rfl fun q _ => by
      have hpoint (τ : Fin S.card → ℝ) :
          (freeGibbsDensityOperator ε β).expectation
              (Common.finiteHilbertOperatorAlgEquiv (Common.quarticVertexSequenceInteractionPicture (fermionEnergy ε) create annihilate S.card q τ)) =
            ∑ pairing : Pairing (2 * S.card),
              flatVertexLegPairingEvaluation ε β q τ pairing := by
        rw [← prod_ofFn_quarticLegOperatorForSequence_eq_quarticVertexSequenceInteractionPicture]
        simpa only [flatVertexLegPairingEvaluation, Combinatorics.Pairing.evaluation,
          flatVertexLegPairValue, timedFieldOperator_quarticLegFieldForSequence] using
          (freeGibbsDensityOperator_expectation_prod_timedFieldOperator_eq_sum_pairing
            ε β (2 * S.card) (quarticLegFieldForSequence q τ))
      rw [intervalIntegral.orderedSimplexIntegral_congr hpoint,
        intervalIntegral.orderedSimplexIntegral_finsetSum _ S.card β _
          (fun pairing _ => continuous_flatVertexLegPairingEvaluation ε β q pairing)]
  rw [Combinatorics.powerSeriesMomentCoeff,
    Common.coeff_normalizeByConstantCoeff_dysonTraceSeries_eq_finiteGibbsExpectation,
    ← freeGibbsDensityOperator_expectation_eq_finiteGibbsExpectation,
    hkey, mul_assoc, hsum]

end Fermionic
end SecondQuantization
