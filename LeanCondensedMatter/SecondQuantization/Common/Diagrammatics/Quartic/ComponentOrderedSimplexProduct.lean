import LeanCondensedMatter.Analysis.OrderedSimplex.FamilyShuffleFintype
import LeanCondensedMatter.Analysis.OrderedSimplex.FinCast
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.ComponentOrderedSimplex

set_option linter.style.header false

/-!
# Ordered-simplex product identity over diagram components

The generic finite-family shuffle identity applies directly to the finite type of connected
component blocks.  No enumeration by `Fin k` is needed: the only transport is the canonical equality
between the sum of component cardinalities and the ambient vertex cardinality.
-/

namespace SecondQuantization
namespace Common

open intervalIntegral
open Combinatorics

variable {Label : Type*} {N : ℕ}

/-- The sum of the component vertex counts is the ambient vertex count. -/
theorem QuarticDiagram.sum_componentCard {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) :
    (∑ B : d.componentPartition.parts, (B : Finset (Fin N)).card) = S.card := by
  rw [Finset.sum_coe_sort]
  exact d.componentPartition.sum_card_parts

/-- Generic finite-family shuffles indexed directly by component blocks are equivalent to the
diagram's ambient component shuffles. -/
noncomputable def QuarticDiagram.componentFamilyShuffleEquiv {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) :
    FamilySlotShuffle (fun B : d.componentPartition.parts => (B : Finset (Fin N)).card) ≃
      d.ComponentShuffle where
  toFun shuffle :=
    { slotEquiv := shuffle.slotEquiv.trans (finCongr d.sum_componentCard)
      strictMono := by
        intro B a b hab
        change (finCongr d.sum_componentCard) (shuffle.slotEquiv ⟨B, a⟩) <
          (finCongr d.sum_componentCard) (shuffle.slotEquiv ⟨B, b⟩)
        exact (strictMono_finCongr d.sum_componentCard) (shuffle.strictMono B hab) }
  invFun shuffle :=
    { slotEquiv := shuffle.slotEquiv.trans (finCongr d.sum_componentCard).symm
      strictMono := by
        intro B a b hab
        change (finCongr d.sum_componentCard).symm (shuffle.slotEquiv ⟨B, a⟩) <
          (finCongr d.sum_componentCard).symm (shuffle.slotEquiv ⟨B, b⟩)
        have hcast : StrictMono (finCongr d.sum_componentCard).symm := by
          simpa using strictMono_finCongr d.sum_componentCard.symm
        exact hcast (shuffle.strictMono B hab) }
  left_inv shuffle := by
    apply FamilySlotShuffle.ext
    apply Equiv.ext
    intro x
    simp
  right_inv shuffle := by
    apply QuarticDiagram.ComponentShuffle.ext
    apply Equiv.ext
    intro x
    simp

/-- Transporting a generic component-indexed family shuffle to ambient diagram coordinates only
precomposes the generic shuffled integrand by the total-cardinality cast. -/
theorem QuarticDiagram.componentShuffleIntegrand_componentFamilyShuffleEquiv
    {S : Finset (Fin N)} (d : QuarticDiagram Label N S)
    (shuffle : FamilySlotShuffle
      (fun B : d.componentPartition.parts => (B : Finset (Fin N)).card))
    (componentIntegrand :
      ∀ B : d.componentPartition.parts, (Fin (B : Finset (Fin N)).card → ℝ) → ℂ)
    (τ : Fin S.card → ℝ) :
    d.componentShuffleIntegrand (d.componentFamilyShuffleEquiv shuffle) componentIntegrand τ =
      shuffle.integrand componentIntegrand
        (fun j => τ (finCongr d.sum_componentCard j)) := by
  classical
  unfold QuarticDiagram.componentShuffleIntegrand FamilySlotShuffle.integrand
    QuarticDiagram.componentTimeAssignment FamilySlotShuffle.timeAssignment
  rfl

/-- One generic component-indexed family-shuffle term equals its ambient diagram-shuffle term. -/
theorem QuarticDiagram.orderedSimplexIntegral_componentFamilyShuffleEquiv
    {S : Finset (Fin N)} (d : QuarticDiagram Label N S)
    (shuffle : FamilySlotShuffle
      (fun B : d.componentPartition.parts => (B : Finset (Fin N)).card))
    (β : ℝ)
    (componentIntegrand :
      ∀ B : d.componentPartition.parts, (Fin (B : Finset (Fin N)).card → ℝ) → ℂ) :
    orderedSimplexIntegral S.card β
        (d.componentShuffleIntegrand (d.componentFamilyShuffleEquiv shuffle) componentIntegrand) =
      orderedSimplexIntegral
        (∑ B : d.componentPartition.parts, (B : Finset (Fin N)).card) β
        (shuffle.integrand componentIntegrand) := by
  calc
    orderedSimplexIntegral S.card β
        (d.componentShuffleIntegrand (d.componentFamilyShuffleEquiv shuffle) componentIntegrand) =
      orderedSimplexIntegral S.card β (fun τ =>
        shuffle.integrand componentIntegrand
          (fun j => τ (finCongr d.sum_componentCard j))) := by
      apply orderedSimplexIntegral_congr
      intro τ
      exact d.componentShuffleIntegrand_componentFamilyShuffleEquiv shuffle componentIntegrand τ
    _ = orderedSimplexIntegral
        (∑ B : d.componentPartition.parts, (B : Finset (Fin N)).card) β
        (shuffle.integrand componentIntegrand) := by
      symm
      simpa using intervalIntegral.orderedSimplexIntegral_cast d.sum_componentCard β
        (shuffle.integrand componentIntegrand)

/-- Reindex the finite sum over ambient diagram component shuffles by generic shuffles indexed
straight by component blocks. -/
theorem QuarticDiagram.sum_componentShuffle_orderedSimplexIntegral_eq_familyShuffle
    {S : Finset (Fin N)} (d : QuarticDiagram Label N S) (β : ℝ)
    (componentIntegrand :
      ∀ B : d.componentPartition.parts, (Fin (B : Finset (Fin N)).card → ℝ) → ℂ) :
    (∑ shuffle : d.ComponentShuffle,
      orderedSimplexIntegral S.card β
        (d.componentShuffleIntegrand shuffle componentIntegrand)) =
      ∑ shuffle : FamilySlotShuffle
        (fun B : d.componentPartition.parts => (B : Finset (Fin N)).card),
        orderedSimplexIntegral
          (∑ B : d.componentPartition.parts, (B : Finset (Fin N)).card) β
          (shuffle.integrand componentIntegrand) := by
  rw [← Equiv.sum_comp d.componentFamilyShuffleEquiv]
  apply Finset.sum_congr rfl
  intro shuffle _
  exact d.orderedSimplexIntegral_componentFamilyShuffleEquiv shuffle β componentIntegrand

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
  rw [d.sum_componentShuffle_orderedSimplexIntegral_eq_familyShuffle β componentIntegrand]
  exact FamilySlotShuffle.sum_orderedSimplexIntegral_integrand_eq_prod_fintype
    (fun B : d.componentPartition.parts => (B : Finset (Fin N)).card)
    β componentIntegrand hcomponent

end Common
end SecondQuantization
