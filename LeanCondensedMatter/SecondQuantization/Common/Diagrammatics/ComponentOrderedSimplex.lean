import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ComponentOrderDecomposition
import LeanCondensedMatter.Analysis.OrderedSimplex.Integral

set_option linter.style.header false

/-!
# Component-shuffle ordered-simplex integrands

An order-preserving component shuffle identifies every component-local time coordinate with one
ambient time slot. This module packages that coordinate restriction, products of component-local
integrands along a shuffle, their continuity, and the finite-sum interchange needed before proving
the full ordered-simplex shuffle product identity.
-/

namespace SecondQuantization
namespace Common

variable {Label : Type*} {N : ℕ}

/-- Restrict an ambient time assignment to the local slots of one component through a shuffle. -/
def QuarticDiagram.componentTimeAssignment {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (shuffle : d.ComponentShuffle)
    (τ : Fin S.card → ℝ) (B : d.componentPartition.parts) :
    Fin (B : Finset (Fin N)).card → ℝ :=
  fun i => τ (shuffle.slotEquiv ⟨B, i⟩)

@[simp]
theorem QuarticDiagram.componentTimeAssignment_apply {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (shuffle : d.ComponentShuffle)
    (τ : Fin S.card → ℝ) (B : d.componentPartition.parts)
    (i : Fin (B : Finset (Fin N)).card) :
    d.componentTimeAssignment shuffle τ B i = τ (shuffle.slotEquiv ⟨B, i⟩) :=
  rfl

/-- Restricting ambient time assignments to one component is continuous. -/
theorem QuarticDiagram.continuous_componentTimeAssignment {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (shuffle : d.ComponentShuffle)
    (B : d.componentPartition.parts) :
    Continuous (fun τ : Fin S.card → ℝ => d.componentTimeAssignment shuffle τ B) := by
  exact continuous_pi fun i => continuous_apply (shuffle.slotEquiv ⟨B, i⟩)

/-- Product of component-local integrands after their time variables are embedded by a shuffle. -/
noncomputable def QuarticDiagram.componentShuffleIntegrand {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (shuffle : d.ComponentShuffle)
    (componentIntegrand :
      ∀ B : d.componentPartition.parts, (Fin (B : Finset (Fin N)).card → ℝ) → ℂ)
    (τ : Fin S.card → ℝ) : ℂ :=
  ∏ B, componentIntegrand B (d.componentTimeAssignment shuffle τ B)

/-- A product of continuous component-local integrands remains continuous after shuffling. -/
theorem QuarticDiagram.continuous_componentShuffleIntegrand {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (shuffle : d.ComponentShuffle)
    (componentIntegrand :
      ∀ B : d.componentPartition.parts, (Fin (B : Finset (Fin N)).card → ℝ) → ℂ)
    (hcomponent : ∀ B, Continuous (componentIntegrand B)) :
    Continuous (d.componentShuffleIntegrand shuffle componentIntegrand) := by
  unfold QuarticDiagram.componentShuffleIntegrand
  exact continuous_finsetProd _ fun B _ =>
    (hcomponent B).comp (d.continuous_componentTimeAssignment shuffle B)

/-- The finite sum over component shuffles commutes with the ambient ordered-simplex integral. -/
theorem QuarticDiagram.orderedSimplexIntegral_sum_componentShuffleIntegrand
    {S : Finset (Fin N)} (d : QuarticDiagram Label N S) (β : ℝ)
    (componentIntegrand :
      ∀ B : d.componentPartition.parts, (Fin (B : Finset (Fin N)).card → ℝ) → ℂ)
    (hcomponent : ∀ B, Continuous (componentIntegrand B)) :
    intervalIntegral.orderedSimplexIntegral S.card β
        (fun τ => ∑ shuffle : d.ComponentShuffle,
          d.componentShuffleIntegrand shuffle componentIntegrand τ) =
      ∑ shuffle : d.ComponentShuffle,
        intervalIntegral.orderedSimplexIntegral S.card β
          (d.componentShuffleIntegrand shuffle componentIntegrand) := by
  classical
  simpa using intervalIntegral.orderedSimplexIntegral_finsetSum
    (Finset.univ : Finset d.ComponentShuffle) S.card β
    (fun shuffle => d.componentShuffleIntegrand shuffle componentIntegrand)
    (fun shuffle _ => d.continuous_componentShuffleIntegrand shuffle componentIntegrand hcomponent)

end Common
end SecondQuantization
