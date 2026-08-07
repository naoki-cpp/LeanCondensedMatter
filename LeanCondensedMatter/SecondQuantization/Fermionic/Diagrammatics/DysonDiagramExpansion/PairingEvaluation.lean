import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.PairingEvaluation
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.DysonDiagramExpansion.Pairing

set_option linter.style.header false

/-!
# Dyson diagram pairing evaluation

This module isolates the physical specialization of the statistics-independent
`Common.pairingEvaluation` API for flattened quartic Dyson legs. The pair kernel is the canonical
free Gibbs density-state expectation; finite Gibbs coordinate formulas remain in `Pairing.lean` as
evaluation and bridge infrastructure.

The existing expanded density-state theorem statements are retained for compatibility. The evaluator
form below is the canonical scalar boundary for subsequent Dyson-to-diagram reindexing.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- Canonical free Gibbs density-state contraction of two flattened quartic Dyson legs. -/
noncomputable def flatVertexLegPairValue {n : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (q : Fin n → QuarticVertexLabel Mode)
    (τ : Fin n → ℝ) (a b : Fin (2 * (2 * n))) : ℂ :=
  (freeGibbsDensityOperator ε β).expectation
    (Common.finiteHilbertOperator
      ((quarticLegOperatorForSequence ε q τ a).comp
        (quarticLegOperatorForSequence ε q τ b)))

/-- Scalar value of one flattened-leg pairing through the shared generic pairing evaluator. -/
noncomputable def flatVertexLegPairingEvaluation {n : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (q : Fin n → QuarticVertexLabel Mode)
    (τ : Fin n → ℝ) (pairing : Pairing (2 * n)) : ℂ :=
  Common.pairingEvaluation pairing (pairing.weight Common.Statistics.fermion)
    (flatVertexLegPairValue ε β q τ)

@[simp]
theorem flatVertexLegPairingEvaluation_eq {n : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (q : Fin n → QuarticVertexLabel Mode)
    (τ : Fin n → ℝ) (pairing : Pairing (2 * n)) :
    flatVertexLegPairingEvaluation ε β q τ pairing =
      pairing.weight Common.Statistics.fermion *
        ∏ pr ∈ pairing.pairs, flatVertexLegPairValue ε β q τ pr.1 pr.2 :=
  rfl

/-- The nested quartic vertex expectation is a sum of generic pairing evaluations specialized to the
canonical free Gibbs density-state pair kernel. -/
theorem freeGibbsDensityOperator_expectation_nestedVertexOperatorComp_eq_sum_pairingEvaluation
    (ε : Mode → ℝ) (β : ℝ) (n : ℕ) (q : Fin n → QuarticVertexLabel Mode)
    (τ : Fin n → ℝ) :
    (freeGibbsDensityOperator ε β).expectation
        (Common.finiteHilbertOperator (nestedVertexOperatorComp ε n q τ)) =
      ∑ pairing : Pairing (2 * n),
        flatVertexLegPairingEvaluation ε β q τ pairing := by
  simpa [flatVertexLegPairingEvaluation, flatVertexLegPairValue, Common.pairingEvaluation] using
    freeGibbsDensityOperator_expectation_nestedVertexOperatorComp_eq_sum_pairing ε β n q τ

/-- Closed form of the canonical flattened-leg pair kernel. -/
theorem flatVertexLegPairValue_eq {n : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (q : Fin n → QuarticVertexLabel Mode)
    (τ : Fin n → ℝ) (a b : Fin (2 * (2 * n))) :
    flatVertexLegPairValue ε β q τ a b =
      Complex.exp ((τ (flatVertexIndex n a) * flatVertexLegEnergyShift ε q a : ℝ) : ℂ) *
        Complex.exp ((τ (flatVertexIndex n b) * flatVertexLegEnergyShift ε q b : ℝ) : ℂ) *
        (freeGibbsDensityOperator ε β).expectation
          (Common.finiteHilbertOperator
            ((quarticLocalLegOperator (q (flatVertexIndex n a)) (flatLocalLeg n a)).comp
              (quarticLocalLegOperator (q (flatVertexIndex n b)) (flatLocalLeg n b)))) := by
  simpa [flatVertexLegPairValue] using
    freeGibbsDensityOperator_expectation_quarticLegOperatorForSequence_pair_eq ε β q τ a b

/-- The canonical flattened-leg pair kernel is continuous in the vertex-time assignment. -/
theorem continuous_flatVertexLegPairValue {n : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (q : Fin n → QuarticVertexLabel Mode)
    (a b : Fin (2 * (2 * n))) :
    Continuous (fun τ : Fin n → ℝ => flatVertexLegPairValue ε β q τ a b) := by
  simpa [flatVertexLegPairValue] using
    continuous_freeGibbsDensityOperator_expectation_quarticLegOperatorForSequence_pair ε β q a b

/-- Generic pairing evaluation of the flattened-leg density-state kernel is continuous in the
vertex-time assignment. -/
theorem continuous_flatVertexLegPairingEvaluation {n : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (q : Fin n → QuarticVertexLabel Mode)
    (pairing : Pairing (2 * n)) :
    Continuous (fun τ : Fin n → ℝ => flatVertexLegPairingEvaluation ε β q τ pairing) := by
  simp only [flatVertexLegPairingEvaluation, Common.pairingEvaluation]
  exact continuous_const.mul (continuous_finsetProd _ fun pr _ =>
    continuous_flatVertexLegPairValue ε β q pr.1 pr.2)

/-- Ordered-simplex integration commutes with the finite pairing sum in the evaluator presentation. -/
theorem
    orderedSimplexIntegral_freeGibbsDensityOperator_expectation_nestedVertexOperatorComp_eq_sum_pairingEvaluation
    (ε : Mode → ℝ) (β t : ℝ) (n : ℕ) (q : Fin n → QuarticVertexLabel Mode) :
    intervalIntegral.orderedSimplexIntegral n t
        (fun τ => (freeGibbsDensityOperator ε β).expectation
          (Common.finiteHilbertOperator (nestedVertexOperatorComp ε n q τ))) =
      ∑ pairing : Pairing (2 * n),
        intervalIntegral.orderedSimplexIntegral n t
          (fun τ => flatVertexLegPairingEvaluation ε β q τ pairing) := by
  rw [intervalIntegral.orderedSimplexIntegral_congr
      (fun τ =>
        freeGibbsDensityOperator_expectation_nestedVertexOperatorComp_eq_sum_pairingEvaluation
          ε β n q τ),
    intervalIntegral.orderedSimplexIntegral_finsetSum _ n t _
      (fun pairing _ => continuous_flatVertexLegPairingEvaluation ε β q pairing)]

/-- `dysonVertexMoment` of the quartic interaction in the canonical generic-evaluator
presentation. Existing expanded-product theorems remain available from `Pairing.lean`. -/
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
            (Common.finiteHilbertOperator
              (nestedVertexOperatorComp ε S.card q τ))) =
      ∑ q : Fin S.card → QuarticVertexLabel Mode, (∏ i, g (q i)) *
        ∑ pairing : Pairing (2 * S.card),
          intervalIntegral.orderedSimplexIntegral S.card β
            (fun τ => flatVertexLegPairingEvaluation ε β q τ pairing) :=
    Finset.sum_congr rfl fun q _ => by
      rw [
        orderedSimplexIntegral_freeGibbsDensityOperator_expectation_nestedVertexOperatorComp_eq_sum_pairingEvaluation
      ]
  rw [dysonVertexMoment_eq_freeGibbsDensityOperator_expectation, hkey, mul_assoc, hsum]

end Fermionic
end SecondQuantization
