import LeanCondensedMatter.Analysis.OrderedSimplex.FamilyShuffleFintype
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.ComponentOrder

set_option linter.style.header false

/-!
# Ordered-simplex factorization over quartic diagram components

An order-preserving component shuffle identifies every component-local time coordinate with one
ambient time slot. The generic coordinate restriction, shuffled-product analysis, and finite-family
ordered-simplex product theorem are owned by `Analysis/OrderedSimplex`; this module keeps the quartic
diagram adapters and their component-product endpoint together.
-/

namespace SecondQuantization
namespace Common

open intervalIntegral
open Combinatorics

variable {Label : Type*} {N : ℕ}

/-- Restrict an ambient time assignment to the local slots of one component through a shuffle. -/
def QuarticDiagram.componentTimeAssignment {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (shuffle : d.ComponentShuffle)
    (τ : Fin S.card → ℝ) (B : d.componentPartition.parts) :
    Fin (B : Finset (Fin N)).card → ℝ :=
  shuffle.timeAssignment τ B

@[simp]
theorem QuarticDiagram.componentTimeAssignment_apply {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (shuffle : d.ComponentShuffle)
    (τ : Fin S.card → ℝ) (B : d.componentPartition.parts)
    (i : Fin (B : Finset (Fin N)).card) :
    d.componentTimeAssignment shuffle τ B i = τ (shuffle.slotEquiv ⟨B, i⟩) :=
  rfl

/-- Product of component-local integrands after their time variables are embedded by a shuffle. -/
noncomputable def QuarticDiagram.componentShuffleIntegrand {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (shuffle : d.ComponentShuffle)
    (componentIntegrand :
      ∀ B : d.componentPartition.parts, (Fin (B : Finset (Fin N)).card → ℝ) → ℂ)
    (τ : Fin S.card → ℝ) : ℂ :=
  shuffle.ambientIntegrand componentIntegrand τ

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
