import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.ComponentOrderDecomposition
import LeanCondensedMatter.Analysis.OrderedSimplex.FamilyShuffleIntegrand

set_option linter.style.header false

/-!
# Component-shuffle ordered-simplex integrands

An order-preserving component shuffle identifies every component-local time coordinate with one
ambient time slot. The generic coordinate restriction and shuffled-product analysis are owned by
`Analysis/OrderedSimplex/FamilyShuffleIntegrand`; this module keeps the quartic diagram adapters.
-/

namespace SecondQuantization
namespace Common

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

end Common
end SecondQuantization
