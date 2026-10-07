import LeanCondensedMatter.Analysis.OrderedSimplex.FamilyShuffle
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.ComponentAmplitude

set_option linter.style.header false

/-!
# Ordered-simplex component factorization for external insertions

The fixed-time Dyson amplitude already factors pointwise into standalone connected-component
amplitudes. This module connects that result to the finite-family ordered-simplex shuffle theorem.

A single ambient interaction order selects one component interaction shuffle. The product of the
standalone component integrals is recovered only after summing over all order-preserving
interleavings of the component-local interaction slots.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Common
open scoped BigOperators

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- Ordered-simplex contribution of one arbitrary external-insertion diagram, before the Dyson
sign. -/
noncomputable def ExternalInsertionWickDiagram.orderedSimplexContribution
    {E n : ℕ} (d : ExternalInsertionWickDiagram Mode E n)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (externalTime : Fin (2 * E) → ℝ) : ℂ :=
  intervalIntegral.orderedSimplexIntegral n β
    (fun σ => d.fixedTimeAmplitude ε β g externalTime σ)

/-- Integrated arbitrary-external-insertion amplitude including the order-`n` Dyson sign. -/
noncomputable def ExternalInsertionWickDiagram.dysonAmplitude
    {E n : ℕ} (d : ExternalInsertionWickDiagram Mode E n)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (externalTime : Fin (2 * E) → ℝ) : ℂ :=
  (-1 : ℂ) ^ n * d.orderedSimplexContribution ε β g externalTime

/-- Integrating the Dyson-signed fixed-time amplitude is the integrated Dyson amplitude. -/
theorem ExternalInsertionWickDiagram.orderedSimplexIntegral_dysonFixedTimeAmplitude
    {E n : ℕ} (d : ExternalInsertionWickDiagram Mode E n)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (externalTime : Fin (2 * E) → ℝ) :
    intervalIntegral.orderedSimplexIntegral n β
        (fun σ => d.dysonFixedTimeAmplitude ε β g externalTime σ) =
      d.dysonAmplitude ε β g externalTime := by
  unfold ExternalInsertionWickDiagram.dysonFixedTimeAmplitude
    ExternalInsertionWickDiagram.dysonAmplitude
    ExternalInsertionWickDiagram.orderedSimplexContribution
  exact intervalIntegral.orderedSimplexIntegral_smul n β
    ((-1 : ℂ) ^ n) (fun σ => d.fixedTimeAmplitude ε β g externalTime σ)

/-- The canonical component interaction shuffle with the ambient `Finset.univ.card`
transported to the definitional ambient slot type `Fin n`. -/
private noncomputable def ExternalInsertionWickDiagram.componentInteractionShuffleToFin
    {E n : ℕ} (d : ExternalInsertionWickDiagram Mode E n) :
    FamilySlotShuffleTo
      (fun B : d.vertexGraph.componentPartition.parts =>
        (interactionSector
          (B : Finset (ExternalInsertionVertex E
            (Finset.univ : Finset (Fin n))))).card)
      n :=
  FamilySlotShuffleTo.castTotalEquiv (by simp) d.componentInteractionShuffle

omit [Fintype Mode] in
/-- The canonical component interaction shuffle pulls an ambient time assignment back to the
canonical component interaction times. -/
private theorem ExternalInsertionWickDiagram.componentInteractionShuffleToFin_timeAssignment
    {E n : ℕ} (d : ExternalInsertionWickDiagram Mode E n)
    (σ : Fin n → ℝ) (B : d.vertexGraph.componentPartition.parts) :
    d.componentInteractionShuffleToFin.timeAssignment σ B =
      d.componentInteractionTime σ B := by
  funext v
  change σ (Fin.cast (by simp) (d.componentInteractionShuffle.slotEquiv ⟨B, v⟩)) =
    σ ((interactionSector
      (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))).orderIsoOfFin
        rfl v).1
  rw [ExternalInsertionDiagram.componentInteractionShuffle_slotEquiv_apply]
  congr 1
  apply Fin.ext
  rw [Finset.orderIsoOfFin_symm_apply, Fin.sort_univ, List.idxOf_finRange]

/-- The pointwise Dyson amplitude is the external regrouping sign times the canonical component
shuffle applied to the standalone component Dyson integrands. -/
theorem ExternalInsertionWickDiagram.dysonFixedTimeAmplitude_eq_componentExternalOrderSign_mul_componentInteractionShuffle_ambientIntegrand
    {E n : ℕ} (d : ExternalInsertionWickDiagram Mode E n)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (blockOrder : d.vertexGraph.componentPartition.parts ≃
      Fin (Fintype.card d.vertexGraph.componentPartition.parts)) :
    d.dysonFixedTimeAmplitude ε β g externalTime σ =
      componentExternalOrderSign d blockOrder *
        d.componentInteractionShuffleToFin.ambientIntegrand
          (fun B localσ =>
            (d.componentWickDiagram B).dysonFixedTimeAmplitude ε β g
              (d.componentExternalTime externalTime B) localσ) σ := by
  rw [d.dysonFixedTimeAmplitude_eq_componentExternalOrderSign_mul_prod_components
    ε β g externalTime σ blockOrder]
  apply congrArg (fun z : ℂ => componentExternalOrderSign d blockOrder * z)
  unfold FamilySlotShuffleTo.ambientIntegrand
  apply Finset.prod_congr rfl
  intro B _
  rw [d.componentInteractionShuffleToFin_timeAssignment σ B]

/-- Summing the ordered-simplex Dyson contribution over all order-preserving interleavings of the
component interaction slots gives the external regrouping sign times the product of the standalone
component Dyson amplitudes. -/
theorem ExternalInsertionWickDiagram.sum_componentInteractionShuffle_dysonIntegral_eq_componentExternalOrderSign_mul_prod_dysonAmplitude
    {E n : ℕ} (d : ExternalInsertionWickDiagram Mode E n)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (externalTime : Fin (2 * E) → ℝ)
    (blockOrder : d.vertexGraph.componentPartition.parts ≃
      Fin (Fintype.card d.vertexGraph.componentPartition.parts))
    (hlocal : ∀ B : d.vertexGraph.componentPartition.parts,
      intervalIntegral.MeasurableLocallyBounded
        (fun localσ =>
          (d.componentWickDiagram B).dysonFixedTimeAmplitude ε β g
            (d.componentExternalTime externalTime B) localσ)) :
    (∑ shuffle : FamilySlotShuffleTo
        (fun B : d.vertexGraph.componentPartition.parts =>
          (interactionSector
            (B : Finset (ExternalInsertionVertex E
              (Finset.univ : Finset (Fin n))))).card)
        n,
      intervalIntegral.orderedSimplexIntegral n β
        (fun σ =>
          componentExternalOrderSign d blockOrder *
            shuffle.ambientIntegrand
              (fun B localσ =>
                (d.componentWickDiagram B).dysonFixedTimeAmplitude ε β g
                  (d.componentExternalTime externalTime B) localσ) σ)) =
      componentExternalOrderSign d blockOrder *
        ∏ B : d.vertexGraph.componentPartition.parts,
          (d.componentWickDiagram B).dysonAmplitude ε β g
            (d.componentExternalTime externalTime B) := by
  classical
  let size : d.vertexGraph.componentPartition.parts → ℕ :=
    fun B =>
      (interactionSector
        (B : Finset (ExternalInsertionVertex E
          (Finset.univ : Finset (Fin n))))).card
  let localIntegrand : ∀ B : d.vertexGraph.componentPartition.parts,
      (Fin (size B) → ℝ) → ℂ :=
    fun B localσ =>
      (d.componentWickDiagram B).dysonFixedTimeAmplitude ε β g
        (d.componentExternalTime externalTime B) localσ
  have hTotal : (∑ B, size B) = n := by
    simpa [size] using
      (sum_interactionSector_card_eq d.vertexGraph)
  have hshuffle :=
    FamilySlotShuffleTo.sum_integral_eq_prod size n hTotal β localIntegrand
      (fun B => by simpa [size, localIntegrand] using hlocal B)
  change
    (∑ shuffle : FamilySlotShuffleTo size n,
      intervalIntegral.orderedSimplexIntegral n β
        (fun σ =>
          componentExternalOrderSign d blockOrder *
            shuffle.ambientIntegrand localIntegrand σ)) =
      componentExternalOrderSign d blockOrder *
        ∏ B : d.vertexGraph.componentPartition.parts,
          (d.componentWickDiagram B).dysonAmplitude ε β g
            (d.componentExternalTime externalTime B)
  simp_rw [intervalIntegral.orderedSimplexIntegral_smul]
  rw [← Finset.mul_sum, hshuffle]
  apply congrArg (fun z : ℂ => componentExternalOrderSign d blockOrder * z)
  apply Finset.prod_congr rfl
  intro B _
  exact d.componentWickDiagram B |>.orderedSimplexIntegral_dysonFixedTimeAmplitude
    ε β g (d.componentExternalTime externalTime B)

end Fermionic
end SecondQuantization
