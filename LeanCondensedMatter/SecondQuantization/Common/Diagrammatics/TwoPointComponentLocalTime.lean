import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPointComponentOrderedSimplex

set_option linter.style.header false

/-!
# Local interaction-time coordinates for two-point components

A two-point component interaction shuffle identifies the dependent family of component-local time
coordinates with the ambient ordered-simplex coordinates. This module supplies the inverse assembly
map, its round-trip laws, and a generic localization interface for scalar factors that depend only on
one component's local interaction times.

The results are statistics-independent. The fermionic two-point expansion can therefore reduce its
componentwise locality problem to proving that the mixed pairing value is unchanged when only times
outside the selected component are varied.
-/

namespace SecondQuantization
namespace Common

variable {ExternalLabel InternalLabel : Type*} {N : ℕ}

noncomputable section

/-- Assemble an ambient interaction-time assignment from one local assignment for every full
component, using the chosen component interaction shuffle. -/
def TwoPointDiagram.interactionTimeAssignmentOfComponents
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (shuffle : d.ComponentInteractionShuffle)
    (componentTime :
      ∀ B : d.componentPartition.parts,
        Fin (d.interactionComponentSize B) → ℝ) :
    Fin S.card → ℝ :=
  fun i =>
    let x := shuffle.slotEquiv.symm i
    componentTime x.1 x.2

@[simp]
theorem TwoPointDiagram.interactionComponentTimeAssignment_ofComponents
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (shuffle : d.ComponentInteractionShuffle)
    (componentTime :
      ∀ B : d.componentPartition.parts,
        Fin (d.interactionComponentSize B) → ℝ)
    (B : d.componentPartition.parts) :
    d.interactionComponentTimeAssignment shuffle
        (d.interactionTimeAssignmentOfComponents shuffle componentTime) B =
      componentTime B := by
  funext i
  simp [TwoPointDiagram.interactionComponentTimeAssignment,
    TwoPointDiagram.interactionTimeAssignmentOfComponents]

@[simp]
theorem TwoPointDiagram.interactionTimeAssignmentOfComponents_componentTimeAssignment
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (shuffle : d.ComponentInteractionShuffle) (τ : Fin S.card → ℝ) :
    d.interactionTimeAssignmentOfComponents shuffle
        (fun B => d.interactionComponentTimeAssignment shuffle τ B) = τ := by
  funext i
  simp [TwoPointDiagram.interactionComponentTimeAssignment,
    TwoPointDiagram.interactionTimeAssignmentOfComponents]

/-- Extend one component-local interaction-time assignment to the ambient slots, setting all other
component times to zero. -/
def TwoPointDiagram.interactionTimeAssignmentOfComponent
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (shuffle : d.ComponentInteractionShuffle) (B : d.componentPartition.parts)
    (componentTime : Fin (d.interactionComponentSize B) → ℝ) :
    Fin S.card → ℝ :=
  d.interactionTimeAssignmentOfComponents shuffle
    (Function.update (fun _ => 0) B componentTime)

@[simp]
theorem TwoPointDiagram.interactionComponentTimeAssignment_ofComponent_self
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (shuffle : d.ComponentInteractionShuffle) (B : d.componentPartition.parts)
    (componentTime : Fin (d.interactionComponentSize B) → ℝ) :
    d.interactionComponentTimeAssignment shuffle
        (d.interactionTimeAssignmentOfComponent shuffle B componentTime) B =
      componentTime := by
  simp [TwoPointDiagram.interactionTimeAssignmentOfComponent]

/-- A scalar ambient-time function is local to component `B` along `shuffle` when changing times
outside the local coordinates selected by `B` does not change its value. -/
def TwoPointDiagram.InteractionComponentLocal
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (shuffle : d.ComponentInteractionShuffle) (B : d.componentPartition.parts)
    (F : (Fin S.card → ℝ) → ℂ) : Prop :=
  ∀ τ υ,
    d.interactionComponentTimeAssignment shuffle τ B =
      d.interactionComponentTimeAssignment shuffle υ B →
    F τ = F υ

/-- Turn an ambient scalar factor into a component-local integrand by extending its local time
coordinates with zero on every other component. -/
def TwoPointDiagram.localizeInteractionComponentIntegrand
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (shuffle : d.ComponentInteractionShuffle) (B : d.componentPartition.parts)
    (F : (Fin S.card → ℝ) → ℂ) :
    (Fin (d.interactionComponentSize B) → ℝ) → ℂ :=
  fun componentTime =>
    F (d.interactionTimeAssignmentOfComponent shuffle B componentTime)

/-- A component-local ambient scalar factor is recovered by evaluating its localized integrand on
the restricted ambient time assignment. -/
theorem TwoPointDiagram.eq_localizeInteractionComponentIntegrand
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (shuffle : d.ComponentInteractionShuffle) (B : d.componentPartition.parts)
    (F : (Fin S.card → ℝ) → ℂ)
    (hF : d.InteractionComponentLocal shuffle B F)
    (τ : Fin S.card → ℝ) :
    F τ = d.localizeInteractionComponentIntegrand shuffle B F
      (d.interactionComponentTimeAssignment shuffle τ B) := by
  apply hF
  symm
  exact d.interactionComponentTimeAssignment_ofComponent_self shuffle B
    (d.interactionComponentTimeAssignment shuffle τ B)

/-- A product of ambient factors that are each local to their own component is the corresponding
component-shuffle integrand of their localized functions. -/
theorem TwoPointDiagram.prod_eq_interactionComponentShuffleIntegrand_localize
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (shuffle : d.ComponentInteractionShuffle)
    (F : ∀ B : d.componentPartition.parts, (Fin S.card → ℝ) → ℂ)
    (hF : ∀ B, d.InteractionComponentLocal shuffle B (F B))
    (τ : Fin S.card → ℝ) :
    (∏ B : d.componentPartition.parts, F B τ) =
      d.interactionComponentShuffleIntegrand shuffle
        (fun B => d.localizeInteractionComponentIntegrand shuffle B (F B)) τ := by
  unfold TwoPointDiagram.interactionComponentShuffleIntegrand
  apply Fintype.prod_congr
  intro B
  exact d.eq_localizeInteractionComponentIntegrand shuffle B (F B) (hF B) τ

end

end Common
end SecondQuantization
