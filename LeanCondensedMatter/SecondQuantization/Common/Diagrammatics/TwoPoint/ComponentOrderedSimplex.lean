import LeanCondensedMatter.Analysis.OrderedSimplex.FamilyShuffleFintype
import LeanCondensedMatter.Analysis.OrderedSimplex.FinCast
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ComponentVertexProduct

set_option linter.style.header false

/-!
# Ordered-simplex shuffles over two-point diagram interaction components

The full components of a two-point diagram partition its interaction vertices, although the unique
external component also contains the two distinguished external vertices. This module therefore
uses the interaction part of every full component as its local ordered-simplex slot block.

The generic finite-family shuffle identity applies directly to the finite type of full components.
No auxiliary enumeration by `Fin k` is needed; only the equality between the total interaction-slot
count and the ambient interaction order must be transported.
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
  fun i => τ (shuffle.slotEquiv ⟨B, i⟩)

@[simp]
theorem TwoPointDiagram.interactionComponentTimeAssignment_apply {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (shuffle : d.ComponentInteractionShuffle)
    (τ : Fin S.card → ℝ) (B : d.componentPartition.parts)
    (i : Fin (d.interactionComponentSize B)) :
    d.interactionComponentTimeAssignment shuffle τ B i =
      τ (shuffle.slotEquiv ⟨B, i⟩) :=
  rfl

/-- Restricting ambient interaction times to one component is continuous. -/
theorem TwoPointDiagram.continuous_interactionComponentTimeAssignment
    {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (shuffle : d.ComponentInteractionShuffle)
    (B : d.componentPartition.parts) :
    Continuous (fun τ : Fin S.card → ℝ =>
      d.interactionComponentTimeAssignment shuffle τ B) := by
  exact continuous_pi fun i => continuous_apply (shuffle.slotEquiv ⟨B, i⟩)

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
  ∏ B, componentIntegrand B
    (d.interactionComponentTimeAssignment shuffle τ B)

/-- A product of continuous component-local interaction-time integrands remains continuous after
shuffling. -/
theorem TwoPointDiagram.continuous_interactionComponentShuffleIntegrand
    {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (shuffle : d.ComponentInteractionShuffle)
    (componentIntegrand :
      ∀ B : d.componentPartition.parts,
        (Fin (d.interactionComponentSize B) → ℝ) → ℂ)
    (hcomponent : ∀ B, Continuous (componentIntegrand B)) :
    Continuous (d.interactionComponentShuffleIntegrand shuffle componentIntegrand) := by
  unfold TwoPointDiagram.interactionComponentShuffleIntegrand
  exact continuous_finsetProd _ fun B _ =>
    (hcomponent B).comp
      (d.continuous_interactionComponentTimeAssignment shuffle B)

/-- Generic family shuffles indexed directly by the full component type are equivalent to ambient
two-point interaction shuffles. -/
noncomputable def TwoPointDiagram.componentInteractionFamilyShuffleEquiv
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    FamilySlotShuffle d.interactionComponentSize ≃ d.ComponentInteractionShuffle :=
  FamilySlotShuffleTo.castTotalEquiv d.sum_interactionComponentSize

/-- Transporting a generic component-indexed family shuffle to ambient interaction coordinates only
precomposes the generic integrand by the total-interaction-cardinality cast. -/
theorem TwoPointDiagram.interactionComponentShuffleIntegrand_componentInteractionFamilyShuffleEquiv
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (shuffle : FamilySlotShuffle d.interactionComponentSize)
    (componentIntegrand :
      ∀ B : d.componentPartition.parts,
        (Fin (d.interactionComponentSize B) → ℝ) → ℂ)
    (τ : Fin S.card → ℝ) :
    d.interactionComponentShuffleIntegrand
        (d.componentInteractionFamilyShuffleEquiv shuffle) componentIntegrand τ =
      shuffle.integrand componentIntegrand
        (fun j => τ (Fin.cast d.sum_interactionComponentSize j)) := by
  classical
  unfold TwoPointDiagram.interactionComponentShuffleIntegrand
    TwoPointDiagram.interactionComponentTimeAssignment
    FamilySlotShuffle.integrand FamilySlotShuffle.timeAssignment
  rfl

/-- One generic component-indexed family-shuffle term equals its ambient two-point interaction-shuffle
term. -/
theorem TwoPointDiagram.orderedSimplexIntegral_componentInteractionFamilyShuffleEquiv
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (shuffle : FamilySlotShuffle d.interactionComponentSize) (β : ℝ)
    (componentIntegrand :
      ∀ B : d.componentPartition.parts,
        (Fin (d.interactionComponentSize B) → ℝ) → ℂ) :
    orderedSimplexIntegral S.card β
        (d.interactionComponentShuffleIntegrand
          (d.componentInteractionFamilyShuffleEquiv shuffle) componentIntegrand) =
      orderedSimplexIntegral
        (∑ B : d.componentPartition.parts, d.interactionComponentSize B) β
        (shuffle.integrand componentIntegrand) := by
  calc
    orderedSimplexIntegral S.card β
        (d.interactionComponentShuffleIntegrand
          (d.componentInteractionFamilyShuffleEquiv shuffle) componentIntegrand) =
      orderedSimplexIntegral S.card β (fun τ =>
        shuffle.integrand componentIntegrand
          (fun j => τ (Fin.cast d.sum_interactionComponentSize j))) := by
      apply orderedSimplexIntegral_congr
      intro τ
      exact d.interactionComponentShuffleIntegrand_componentInteractionFamilyShuffleEquiv
        shuffle componentIntegrand τ
    _ = orderedSimplexIntegral
        (∑ B : d.componentPartition.parts, d.interactionComponentSize B) β
        (shuffle.integrand componentIntegrand) := by
      symm
      exact intervalIntegral.orderedSimplexIntegral_cast
        d.sum_interactionComponentSize β (shuffle.integrand componentIntegrand)

/-- Reindex the finite sum over ambient interaction shuffles by generic shuffles indexed directly by
full component blocks. -/
theorem TwoPointDiagram.sum_componentInteractionShuffle_orderedSimplexIntegral_eq_familyShuffle
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S) (β : ℝ)
    (componentIntegrand :
      ∀ B : d.componentPartition.parts,
        (Fin (d.interactionComponentSize B) → ℝ) → ℂ) :
    (∑ shuffle : d.ComponentInteractionShuffle,
      orderedSimplexIntegral S.card β
        (d.interactionComponentShuffleIntegrand shuffle componentIntegrand)) =
      ∑ shuffle : FamilySlotShuffle d.interactionComponentSize,
        orderedSimplexIntegral
          (∑ B : d.componentPartition.parts, d.interactionComponentSize B) β
          (shuffle.integrand componentIntegrand) := by
  rw [← Equiv.sum_comp d.componentInteractionFamilyShuffleEquiv]
  apply Finset.sum_congr rfl
  intro shuffle _
  exact d.orderedSimplexIntegral_componentInteractionFamilyShuffleEquiv
    shuffle β componentIntegrand

/-- Finite-family ordered-simplex shuffle product identity for the interaction parts of all full
two-point components. -/
theorem TwoPointDiagram.sum_componentInteractionShuffle_orderedSimplexIntegral_eq_prod
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
  have hfamily :=
    FamilySlotShuffle.sum_orderedSimplexIntegral_integrand_eq_prod_fintype
      (ι := d.componentPartition.parts)
      d.interactionComponentSize β componentIntegrand hcomponent
  calc
    (∑ shuffle : d.ComponentInteractionShuffle,
      orderedSimplexIntegral S.card β
        (d.interactionComponentShuffleIntegrand shuffle componentIntegrand)) =
      ∑ shuffle : FamilySlotShuffle d.interactionComponentSize,
        orderedSimplexIntegral
          (∑ B : d.componentPartition.parts, d.interactionComponentSize B) β
          (shuffle.integrand componentIntegrand) :=
      d.sum_componentInteractionShuffle_orderedSimplexIntegral_eq_familyShuffle
        β componentIntegrand
    _ = ∏ B : d.componentPartition.parts,
        orderedSimplexIntegral (d.interactionComponentSize B) β
          (componentIntegrand B) := hfamily

end

end Common
end SecondQuantization
