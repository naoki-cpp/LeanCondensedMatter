import LeanCondensedMatter.Analysis.OrderedSimplex.FamilyShuffleFintype
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Components.ComponentVertexProduct

set_option linter.style.header false

/-!
# Ordered-simplex shuffles over two-point diagram interaction components

The full components of a two-point diagram partition its interaction vertices, although the unique
external component also contains the two distinguished external vertices. This module therefore
uses the interaction part of every full component as its local ordered-simplex slot block.

The generic coordinate restriction, shuffled-product analysis, and finite-family ordered-simplex
identity are owned by `Analysis/OrderedSimplex`; this module keeps the two-point diagram adapters and
the interaction-component cardinality bridge.
-/

namespace SecondQuantization
namespace Common

open intervalIntegral
open Combinatorics

variable {ExternalLabel InternalLabel : Type*} {N : ℕ}

noncomputable section

/-- Number of interaction-time slots belonging to one full component. -/
abbrev TwoPointDiagram.interactionComponentSize {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : d.componentPartition.parts) : ℕ :=
  (TwoPointDiagram.interactionPart
    (B : Finset (TwoPointVertex S))).card

/-- An order-preserving interleaving of all component-local interaction slots into the ambient
interaction-time slots. -/
abbrev TwoPointDiagram.ComponentInteractionShuffle {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) :=
  FamilySlotShuffleTo d.interactionComponentSize S.card

/-- The component-local interaction-slot family has the ambient number of interaction vertices. -/
theorem TwoPointDiagram.sum_interactionComponentSize {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    (∑ B : d.componentPartition.parts, d.interactionComponentSize B) = S.card := by
  calc
    (∑ B : d.componentPartition.parts, d.interactionComponentSize B) =
        Fintype.card
          (Σ B : d.componentPartition.parts,
            ↥(TwoPointDiagram.interactionPart
              (B : Finset (TwoPointVertex S)))) := by
      simp [Fintype.card_sigma]
    _ = Fintype.card ↥S :=
      Fintype.card_congr d.interactionVertexComponentEquiv.symm
    _ = S.card := Fintype.card_coe S

/-- Restrict an ambient interaction-time assignment to the local slots of one full component. -/
def TwoPointDiagram.interactionComponentTimeAssignment {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (shuffle : d.ComponentInteractionShuffle)
    (τ : Fin S.card → ℝ) (B : d.componentPartition.parts) :
    Fin (d.interactionComponentSize B) → ℝ :=
  shuffle.timeAssignment τ B

@[simp]
theorem TwoPointDiagram.interactionComponentTimeAssignment_apply {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (shuffle : d.ComponentInteractionShuffle)
    (τ : Fin S.card → ℝ) (B : d.componentPartition.parts)
    (i : Fin (d.interactionComponentSize B)) :
    d.interactionComponentTimeAssignment shuffle τ B i =
      τ (shuffle.slotEquiv ⟨B, i⟩) :=
  rfl

/-- Product of component-local interaction-time integrands after embedding their coordinates by a
shuffle. -/
def TwoPointDiagram.interactionComponentShuffleIntegrand
    {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (shuffle : d.ComponentInteractionShuffle)
    (componentIntegrand :
      ∀ B : d.componentPartition.parts,
        (Fin (d.interactionComponentSize B) → ℝ) → ℂ)
    (τ : Fin S.card → ℝ) : ℂ :=
  shuffle.ambientIntegrand componentIntegrand τ

/-- Finite-family ordered-simplex shuffle product identity for the interaction parts of all full
two-point components. -/
theorem TwoPointDiagram.sum_componentShuffleIntegral_eq_prod
    {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) (β : ℝ)
    (componentIntegrand :
      ∀ B : d.componentPartition.parts,
        (Fin (d.interactionComponentSize B) → ℝ) → ℂ)
    (hcomponent : ∀ B, Continuous (componentIntegrand B)) :
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
    FamilySlotShuffleTo.sum_orderedSimplexIntegral_ambientIntegrand_eq_prod_fintype
      (ι := d.componentPartition.parts) d.interactionComponentSize S.card
      d.sum_interactionComponentSize β componentIntegrand hcomponent

end

end Common
end SecondQuantization
