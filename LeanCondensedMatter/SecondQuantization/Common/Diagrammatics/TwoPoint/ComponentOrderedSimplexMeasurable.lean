import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ComponentOrderedSimplex

set_option linter.style.header false

/-!
# Measurable bounded ordered-simplex shuffles over two-point components

The generic arbitrary-finite-index family shuffle theorem applies directly to the finite type of
full two-point component blocks, so no auxiliary finite presentation or component enumeration is
required.
-/

namespace SecondQuantization
namespace Common

open intervalIntegral
open Combinatorics

variable {ExternalLabel InternalLabel : Type*} {N : ℕ}

noncomputable section

/-- A product of measurable locally bounded component integrands remains measurable locally bounded
after any ambient interaction-component shuffle. -/
theorem TwoPointDiagram.measurableLocallyBounded_interactionComponentShuffleIntegrand
    {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (shuffle : d.ComponentInteractionShuffle)
    (componentIntegrand :
      ∀ B : d.componentPartition.parts,
        (Fin (d.interactionComponentSize B) → ℝ) → ℂ)
    (hcomponent : ∀ B, MeasurableLocallyBounded (componentIntegrand B)) :
    MeasurableLocallyBounded
      (d.interactionComponentShuffleIntegrand shuffle componentIntegrand) := by
  classical
  have hMeas : Measurable
      (d.interactionComponentShuffleIntegrand shuffle componentIntegrand) := by
    unfold TwoPointDiagram.interactionComponentShuffleIntegrand
    exact Finset.measurable_prod _ fun B _ =>
      (hcomponent B).1.comp
        (d.continuous_interactionComponentTimeAssignment shuffle B).measurable
  refine ⟨hMeas, ?_⟩
  intro R hR
  choose C hC0 hC using fun B => (hcomponent B).2 R hR
  refine ⟨∏ B, C B, Finset.prod_nonneg fun B _ => hC0 B, ?_⟩
  intro τ hτ
  have hmem (B : d.componentPartition.parts) :
      d.interactionComponentTimeAssignment shuffle τ B ∈
        orderedSimplexTimeCube (d.interactionComponentSize B) R := by
    rw [orderedSimplexTimeCube, Set.mem_Icc] at hτ ⊢
    exact ⟨fun i => hτ.1 (shuffle.slotEquiv ⟨B, i⟩),
      fun i => hτ.2 (shuffle.slotEquiv ⟨B, i⟩)⟩
  rw [TwoPointDiagram.interactionComponentShuffleIntegrand, norm_prod]
  exact Finset.prod_le_prod (fun B _ => norm_nonneg _)
    (fun B _ => hC B _ (hmem B))

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
  rw [d.sum_componentInteractionShuffle_orderedSimplexIntegral_eq_familyShuffle
    β componentIntegrand]
  exact
    FamilySlotShuffle.sum_orderedSimplexIntegral_integrand_eq_prod_fintype_of_measurableLocallyBounded
      (ι := d.componentPartition.parts)
      d.interactionComponentSize β componentIntegrand hcomponent

end

end Common
end SecondQuantization
