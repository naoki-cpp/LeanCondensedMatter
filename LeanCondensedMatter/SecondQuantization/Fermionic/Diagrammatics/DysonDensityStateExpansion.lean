import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.DysonDiagramExpansion

set_option linter.style.header false

/-!
# Density-state interfaces for the fermionic Dyson diagram expansion

This module exposes the pairing kernels used by the quartic Dyson expansion directly through the
canonical free Gibbs density operator. The existing coordinate-expectation proofs remain internal
to `DysonDiagramExpansion.lean` during the destructive E4 migration.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics

variable {Mode : Type*} [DecidableEq Mode] [LinearOrder Mode] [Fintype Mode]

/-- The nested quartic vertex product satisfies the pairing expansion through the canonical free
Gibbs density-state expectation. -/
theorem freeGibbsDensityOperator_expectation_nestedVertexOperatorComp_eq_sum_pairing
    (ε : Mode → ℝ) (β : ℝ) (n : ℕ) (q : Fin n → QuarticVertexLabel Mode)
    (τ : Fin n → ℝ) :
    (freeGibbsDensityOperator ε β).expectation
        (Common.finiteHilbertOperator (nestedVertexOperatorComp ε n q τ)) =
      ∑ pairing : Combinatorics.Pairing (2 * n),
        pairing.weight Common.Statistics.fermion *
          ∏ pr ∈ pairing.pairs,
            (freeGibbsDensityOperator ε β).expectation
              (Common.finiteHilbertOperator
                ((quarticLegOperatorForSequence ε q τ pr.1).comp
                  (quarticLegOperatorForSequence ε q τ pr.2))) := by
  simpa only [freeGibbsDensityOperator_expectation_eq_freeGibbsExpectation] using
    freeGibbsExpectation_nestedVertexOperatorComp_eq_sum_pairing ε β n q τ

/-- A pair of evolved flattened legs has the expected exponential prefactor through the canonical
free Gibbs density-state expectation. -/
theorem freeGibbsDensityOperator_expectation_quarticLegOperatorForSequence_pair_eq
    {n : ℕ} (ε : Mode → ℝ) (β : ℝ) (q : Fin n → QuarticVertexLabel Mode)
    (τ : Fin n → ℝ) (a b : Fin (2 * (2 * n))) :
    (freeGibbsDensityOperator ε β).expectation
        (Common.finiteHilbertOperator
          ((quarticLegOperatorForSequence ε q τ a).comp
            (quarticLegOperatorForSequence ε q τ b))) =
      Complex.exp ((τ (flatVertexIndex n a) * flatVertexLegEnergyShift ε q a : ℝ) : ℂ) *
        Complex.exp ((τ (flatVertexIndex n b) * flatVertexLegEnergyShift ε q b : ℝ) : ℂ) *
        (freeGibbsDensityOperator ε β).expectation
          (Common.finiteHilbertOperator
            ((quarticLocalLegOperator (q (flatVertexIndex n a)) (flatLocalLeg n a)).comp
              (quarticLocalLegOperator (q (flatVertexIndex n b)) (flatLocalLeg n b))) := by
  simpa only [freeGibbsDensityOperator_expectation_eq_freeGibbsExpectation] using
    freeGibbsExpectation_quarticLegOperatorForSequence_pair_eq ε β q τ a b

/-- The canonical density-state pair value is continuous in the vertex-time assignment. -/
theorem continuous_freeGibbsDensityOperator_expectation_quarticLegOperatorForSequence_pair
    {n : ℕ} (ε : Mode → ℝ) (β : ℝ) (q : Fin n → QuarticVertexLabel Mode)
    (a b : Fin (2 * (2 * n))) :
    Continuous (fun τ : Fin n → ℝ =>
      (freeGibbsDensityOperator ε β).expectation
        (Common.finiteHilbertOperator
          ((quarticLegOperatorForSequence ε q τ a).comp
            (quarticLegOperatorForSequence ε q τ b)))) := by
  simpa only [freeGibbsDensityOperator_expectation_eq_freeGibbsExpectation] using
    continuous_freeGibbsExpectation_quarticLegOperatorForSequence_pair ε β q a b

/-- The ordered-simplex integral of the canonical density-state nested-vertex expectation is the
sum of the integrated canonical density-state pairing products. -/
theorem orderedSimplexIntegral_freeGibbsDensityOperator_expectation_nestedVertexOperatorComp_eq_sum_pairing
    (ε : Mode → ℝ) (β t : ℝ) (n : ℕ) (q : Fin n → QuarticVertexLabel Mode) :
    intervalIntegral.orderedSimplexIntegral n t
        (fun τ => (freeGibbsDensityOperator ε β).expectation
          (Common.finiteHilbertOperator (nestedVertexOperatorComp ε n q τ))) =
      ∑ pairing : Combinatorics.Pairing (2 * n),
        pairing.weight Common.Statistics.fermion *
          intervalIntegral.orderedSimplexIntegral n t
            (fun τ => ∏ pr ∈ pairing.pairs,
              (freeGibbsDensityOperator ε β).expectation
                (Common.finiteHilbertOperator
                  ((quarticLegOperatorForSequence ε q τ pr.1).comp
                    (quarticLegOperatorForSequence ε q τ pr.2)))) := by
  simpa only [freeGibbsDensityOperator_expectation_eq_freeGibbsExpectation] using
    orderedSimplexIntegral_freeGibbsExpectation_nestedVertexOperatorComp_eq_sum_pairing
      ε β t n q

/-- The quartic Dyson vertex moment as a vertex-label/pairing sum whose contractions are canonical
free Gibbs density-state expectations. -/
theorem dysonVertexMoment_quarticInteraction_eq_sum_vertexLabel_pairing_densityState
    {α : Type*} [DecidableEq α] (ε : Mode → ℝ) (β : ℝ)
    (g : QuarticVertexLabel Mode → ℂ) (S : Finset α) :
    dysonVertexMoment ε β (quarticInteraction g) S =
      (S.card.factorial : ℂ) * (-1 : ℂ) ^ S.card *
        ∑ q : Fin S.card → QuarticVertexLabel Mode, (∏ i, g (q i)) *
          ∑ pairing : Combinatorics.Pairing (2 * S.card),
            pairing.weight Common.Statistics.fermion *
              intervalIntegral.orderedSimplexIntegral S.card β (fun τ =>
                ∏ pr ∈ pairing.pairs,
                  (freeGibbsDensityOperator ε β).expectation
                    (Common.finiteHilbertOperator
                      ((quarticLegOperatorForSequence ε q τ pr.1).comp
                        (quarticLegOperatorForSequence ε q τ pr.2)))) := by
  simpa only [freeGibbsDensityOperator_expectation_eq_freeGibbsExpectation] using
    dysonVertexMoment_quarticInteraction_eq_sum_vertexLabel_pairing ε β g S

end Fermionic
end SecondQuantization
