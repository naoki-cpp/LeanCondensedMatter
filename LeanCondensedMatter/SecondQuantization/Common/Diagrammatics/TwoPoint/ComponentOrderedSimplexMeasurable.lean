import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ComponentOrderedSimplex

set_option linter.style.header false

/-!
# Measurable bounded ordered-simplex shuffles over two-point components

The generic arbitrary-finite-index ambient family-shuffle theorem applies directly to the finite
type of full two-point component blocks.
-/

namespace SecondQuantization
namespace Common

open intervalIntegral
open Combinatorics

variable {ExternalLabel InternalLabel : Type*} {N : ℕ}

noncomputable section

/-- Finite-family ordered-simplex shuffle product identity for two-point interaction components under
measurable local boundedness. -/
theorem TwoPointDiagram.sum_componentInteractionShuffle_orderedSimplexIntegral_eq_prod_of_measurableLocallyBounded
    {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) (β : ℝ)
    (componentIntegrand :
      ∀ B : d.componentPartition.parts,
        (Fin (d.interactionComponentSize B) → ℝ) → ℂ)
    (hcomponent : ∀ B, MeasurableLocallyBounded (componentIntegrand B)) :
    (∑ shuffle : d.ComponentInteractionShuffle,
      orderedSimplexIntegral S.card β
        (d.interactionComponentShuffleIntegrand shuffle componentIntegrand)) =
      ∏ B : d.componentPartition.parts,
        orderedSimplexIntegral (d.interactionComponentSize B) β
          (componentIntegrand B) := by
  change
    (∑ shuffle : FamilySlotShuffleTo d.interactionComponentSize S.card,
      orderedSimplexIntegral S.card β
        (shuffle.ambientIntegrand componentIntegrand)) =
      ∏ B : d.componentPartition.parts,
        orderedSimplexIntegral (d.interactionComponentSize B) β
          (componentIntegrand B)
  exact
    FamilySlotShuffleTo.sum_orderedSimplexIntegral_ambientIntegrand_eq_prod_fintype_of_measurableLocallyBounded
      (ι := d.componentPartition.parts) d.interactionComponentSize S.card
      d.sum_interactionComponentSize β componentIntegrand hcomponent

end

end Common
end SecondQuantization
