import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPointComponentOrderedSimplex

set_option linter.style.header false

/-!
# Measurable bounded ordered-simplex shuffles over two-point components

This module transports the generic measurable-locally-bounded family shuffle theorem through the
canonical finite presentation of two-point diagram components.
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
  classical
  let p := TwoPointDiagram.FiniteInteractionComponentPresentation.canonical d
  calc
    (∑ shuffle : d.ComponentInteractionShuffle,
        orderedSimplexIntegral S.card β
          (d.interactionComponentShuffleIntegrand shuffle componentIntegrand)) =
      ∑ shuffle : FamilySlotShuffle p.size,
        orderedSimplexIntegral (∑ i, p.size i) β
          (shuffle.integrand (fun i => componentIntegrand (p.partsEquiv i))) :=
      p.sum_componentShuffle_orderedSimplexIntegral β componentIntegrand
    _ = ∏ i,
        orderedSimplexIntegral (p.size i) β
          (componentIntegrand (p.partsEquiv i)) :=
      FamilySlotShuffle.sum_orderedSimplexIntegral_integrand_eq_prod_of_measurableLocallyBounded
        _ p.size β (fun i => componentIntegrand (p.partsEquiv i))
        (fun i => hcomponent (p.partsEquiv i))
    _ = ∏ B : d.componentPartition.parts,
        orderedSimplexIntegral (d.interactionComponentSize B) β
          (componentIntegrand B) := by
      refine Fintype.prod_equiv p.partsEquiv _ _ ?_
      intro i
      rfl

end

end Common
end SecondQuantization
