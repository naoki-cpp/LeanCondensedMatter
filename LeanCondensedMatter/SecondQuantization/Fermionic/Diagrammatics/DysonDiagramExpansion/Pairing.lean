import LeanCondensedMatter.Combinatorics.PerfectPairing.Evaluation
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.DysonDiagramExpansion.Core
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.Quartic
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.Quartic.LegFamily
import LeanCondensedMatter.Analysis.PowerSeries.Moment
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.DysonTraceSeries
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.TimedFieldContraction
import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteGibbsExpectationBridge

set_option linter.style.header false

/-!
# Dyson diagram expansion: canonical pairing evaluation

The fermionic operator-flattening identity is a proof-local step of the Dyson-moment endpoint.
Public Dyson pairing statements use the combinatorics-owned `Pairing.evaluation` boundary with
the finite Gibbs expectation pair kernel at explicit μ = 0.
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

/-- μ = 0 grand-canonical contraction of two flattened quartic Dyson legs. -/
noncomputable def flatVertexLegPairValue {n : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (q : Fin n → QuarticVertexLabel Mode)
    (τ : Fin n → ℝ) (a b : Fin (2 * (2 * n))) : ℂ :=
  grandCanonicalTimedFieldPairContraction ε β 0
    (quarticLegFieldForSequence q τ a) (quarticLegFieldForSequence q τ b)

/-- Canonical scalar value of a flattened-leg pairing. -/
noncomputable def flatVertexLegPairingEvaluation {n : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (q : Fin n → QuarticVertexLabel Mode)
    (τ : Fin n → ℝ) (pairing : Pairing (2 * n)) : ℂ :=
  pairing.evaluation (pairing.weight Common.Statistics.fermion)
    (flatVertexLegPairValue ε β q τ)

/-! ## Pair-kernel regularity -/

/-- Closed form of the μ = 0 flattened-leg pair kernel. -/
theorem flatVertexLegPairValue_eq {n : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (q : Fin n → QuarticVertexLabel Mode)
    (τ : Fin n → ℝ) (a b : Fin (2 * (2 * n))) :
    flatVertexLegPairValue ε β q τ a b =
      Complex.exp ((τ (flatVertexIndex n a) * quarticLegEnergyShiftForSequence ε q a : ℝ) : ℂ) *
        Complex.exp ((τ (flatVertexIndex n b) * quarticLegEnergyShiftForSequence ε q b : ℝ) : ℂ) *
        Common.finiteGibbsExpectation (fermionEnergy ε) β
          ((quarticLocalLegOperator (q (flatVertexIndex n a)) (flatLocalLeg n a)).comp
            (quarticLocalLegOperator (q (flatVertexIndex n b)) (flatLocalLeg n b))) := by
  simpa [flatVertexLegPairValue, grandCanonicalTimedFieldPairContraction_eq,
    quarticLegFieldForSequence, quarticLegEnergyShiftForSequence, sub_zero,
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


/-- The order-n quartic Dyson coefficient has a grand-canonical Wick pairing
expansion at arbitrary μ. Physical imaginary-time evolution is generated by
fermionEnergy ε; only the finite Gibbs weight uses ε - μ.

Unlike dysonTraceSeries, whose single energy parameter controls both evolution
and the Boltzmann weight, this coefficient identity keeps the two roles separate. -/
theorem finiteGibbsExpectation_dysonCoeff_quarticInteraction_eq_sum_pairing_explicitMu
    {α : Type*} (ε : Mode → ℝ) (β μ : ℝ)
    (g : QuarticVertexLabel Mode → ℂ) (S : Finset α) :
    Common.finiteGibbsExpectation (fermionEnergy (fun i => ε i - μ)) β
        (Common.dysonCoeff (fermionEnergy ε) (quarticInteraction g) S.card β) =
      (-1 : ℂ) ^ S.card *
        ∑ q : Fin S.card → QuarticVertexLabel Mode, (∏ i, g (q i)) *
          ∑ pairing : Pairing (2 * S.card),
            intervalIntegral.orderedSimplexIntegral S.card β
              (fun τ =>
                pairing.evaluation (pairing.weight Common.Statistics.fermion)
                  (fun a b => grandCanonicalTimedFieldPairContraction ε β μ
                    (quarticLegFieldForSequence q τ a)
                    (quarticLegFieldForSequence q τ b))) := by
  classical
  have hkey :=
    finiteGibbsExpectation_comp_dysonCoeff_quarticInteraction
      ε (fermionEnergy (fun i => ε i - μ)) β g S.card β LinearMap.id
  simp only [LinearMap.id_comp] at hkey
  have hcontinuous (q : Fin S.card → QuarticVertexLabel Mode)
      (pairing : Pairing (2 * S.card)) :
      Continuous (fun τ : Fin S.card → ℝ =>
        pairing.evaluation (pairing.weight Common.Statistics.fermion)
          (fun a b => grandCanonicalTimedFieldPairContraction ε β μ
            (quarticLegFieldForSequence q τ a)
            (quarticLegFieldForSequence q τ b))) := by
    simp only [Combinatorics.Pairing.evaluation]
    exact continuous_const.mul (continuous_finsetProd _ fun pr _ => by
      simp only [grandCanonicalTimedFieldPairContraction_eq,
        quarticLegFieldForSequence]
      fun_prop)
  have hsum :
      (∑ q : Fin S.card → QuarticVertexLabel Mode, (∏ i, g (q i)) *
        intervalIntegral.orderedSimplexIntegral S.card β
          (fun τ => Common.finiteGibbsExpectation (fermionEnergy (fun i => ε i - μ)) β
            (Common.quarticVertexSequenceInteractionPicture
              (fermionEnergy ε) create annihilate S.card q τ))) =
      ∑ q : Fin S.card → QuarticVertexLabel Mode, (∏ i, g (q i)) *
        ∑ pairing : Pairing (2 * S.card),
          intervalIntegral.orderedSimplexIntegral S.card β
            (fun τ =>
              pairing.evaluation (pairing.weight Common.Statistics.fermion)
                (fun a b => grandCanonicalTimedFieldPairContraction ε β μ
                  (quarticLegFieldForSequence q τ a)
                  (quarticLegFieldForSequence q τ b))) := by
    apply Finset.sum_congr rfl
    intro q _
    apply congrArg (fun z : ℂ => (∏ i, g (q i)) * z)
    have hpoint (τ : Fin S.card → ℝ) :
        Common.finiteGibbsExpectation (fermionEnergy (fun i => ε i - μ)) β
          (Common.quarticVertexSequenceInteractionPicture
            (fermionEnergy ε) create annihilate S.card q τ) =
          ∑ pairing : Pairing (2 * S.card),
            pairing.evaluation (pairing.weight Common.Statistics.fermion)
              (fun a b => grandCanonicalTimedFieldPairContraction ε β μ
                (quarticLegFieldForSequence q τ a)
                (quarticLegFieldForSequence q τ b)) := by
      rw [← prod_ofFn_quarticLegOperatorForSequence_eq_quarticVertexSequenceInteractionPicture]
      have hwick := grandCanonicalGibbsExpectation_prod_timedFieldOperator_eq_sum_pairing
        ε β μ (2 * S.card) (quarticLegFieldForSequence q τ)
      simpa only [grandCanonicalTimedFieldPairContraction,
        Combinatorics.Pairing.evaluation,
        timedFieldOperator_quarticLegFieldForSequence] using hwick
    rw [intervalIntegral.orderedSimplexIntegral_congr hpoint,
      intervalIntegral.orderedSimplexIntegral_finsetSum _ S.card β _
        (fun pairing _ => hcontinuous q pairing)]
  rw [hkey, hsum]


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
  rw [Combinatorics.powerSeriesMomentCoeff,
    Common.coeff_normalizeByConstantCoeff_dysonTraceSeries_eq_finiteGibbsExpectation]
  have hgeneral :=
    finiteGibbsExpectation_dysonCoeff_quarticInteraction_eq_sum_pairing_explicitMu
      ε β 0 g S
  simp only [sub_zero] at hgeneral
  rw [hgeneral]
  simp only [mul_assoc]
  apply congrArg (fun z : ℂ => (S.card.factorial : ℂ) * ((-1 : ℂ) ^ S.card * z))
  apply Finset.sum_congr rfl
  intro q _
  apply congrArg (fun z : ℂ => (∏ i, g (q i)) * z)
  apply Finset.sum_congr rfl
  intro pairing _
  apply intervalIntegral.orderedSimplexIntegral_congr
  intro τ
  simp only [flatVertexLegPairingEvaluation, flatVertexLegPairValue,
    Combinatorics.Pairing.evaluation, grandCanonicalTimedFieldPairContraction,
    sub_zero]
end Fermionic
end SecondQuantization
