import LeanCondensedMatter.Analysis.OrderedSimplex.FamilyShuffleFintype
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.ComponentOrderedSimplex

set_option linter.style.header false

/-!
# Ordered-simplex product identity over diagram components

The generic finite-family ambient-shuffle identity applies directly to the finite type of connected
component blocks. The only domain-specific input is that connected components partition the ambient
vertex set.
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
  change
    (∑ shuffle : FamilySlotShuffleTo
        (fun B : d.componentPartition.parts => (B : Finset (Fin N)).card) S.card,
      orderedSimplexIntegral S.card β
        (shuffle.ambientIntegrand componentIntegrand)) =
      ∏ B : d.componentPartition.parts,
        orderedSimplexIntegral (B : Finset (Fin N)).card β (componentIntegrand B)
  have hcard :
      (∑ B : d.componentPartition.parts, (B : Finset (Fin N)).card) = S.card := by
    rw [Finset.sum_coe_sort]
    exact d.componentPartition.sum_card_parts
  exact
    FamilySlotShuffleTo.sum_orderedSimplexIntegral_ambientIntegrand_eq_prod_fintype
      (ι := d.componentPartition.parts)
      (fun B => (B : Finset (Fin N)).card) S.card hcard β componentIntegrand hcomponent

end Common
end SecondQuantization
