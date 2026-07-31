import LeanCondensedMatter.Analysis.OrderedSimplex.FamilyShuffle
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.FiniteComponentOrderedSimplex

set_option linter.style.header false

/-!
# Ordered-simplex product identity over diagram components

The finite-family shuffle identity transports through the canonical enumeration of the connected
component blocks. The sum of all shuffled ambient ordered-simplex integrals is therefore the product
of the component-local ordered-simplex integrals.
-/

namespace SecondQuantization
namespace Common

open intervalIntegral
open Combinatorics

variable {Label : Type*} {N : ℕ}

/-- General component-shuffle ordered-simplex product identity. -/
theorem QuarticDiagram.sum_componentShuffle_orderedSimplexIntegral_eq_prod
    {S : Finset (Fin N)} (d : QuarticDiagram Label N S) (β : ℝ)
    (componentIntegrand :
      ∀ B : d.componentPartition.parts, (Fin (B : Finset (Fin N)).card → ℝ) → ℂ)
    (hcomponent : ∀ B, Continuous (componentIntegrand B)) :
    (∑ shuffle : d.ComponentShuffle,
      orderedSimplexIntegral S.card β
        (d.componentShuffleIntegrand shuffle componentIntegrand)) =
      ∏ B : d.componentPartition.parts,
        orderedSimplexIntegral (B : Finset (Fin N)).card β (componentIntegrand B) := by
  classical
  let p := QuarticDiagram.FiniteComponentPresentation.canonical d
  calc
    (∑ shuffle : d.ComponentShuffle,
        orderedSimplexIntegral S.card β
          (d.componentShuffleIntegrand shuffle componentIntegrand)) =
      ∑ shuffle : FamilySlotShuffle p.size,
        orderedSimplexIntegral (∑ i, p.size i) β
          (shuffle.integrand (fun i => componentIntegrand (p.partsEquiv i))) :=
      p.sum_componentShuffle_orderedSimplexIntegral β componentIntegrand
    _ = ∏ i,
        orderedSimplexIntegral (p.size i) β
          (componentIntegrand (p.partsEquiv i)) :=
      FamilySlotShuffle.sum_orderedSimplexIntegral_integrand_eq_prod
        _ p.size β (fun i => componentIntegrand (p.partsEquiv i))
        (fun i => hcomponent (p.partsEquiv i))
    _ = ∏ B : d.componentPartition.parts,
        orderedSimplexIntegral (B : Finset (Fin N)).card β (componentIntegrand B) := by
      refine Fintype.prod_equiv p.partsEquiv _ _ ?_
      intro i
      rfl

end Common
end SecondQuantization
