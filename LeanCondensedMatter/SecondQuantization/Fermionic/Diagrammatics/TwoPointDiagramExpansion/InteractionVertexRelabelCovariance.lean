import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.ComponentShufflePermutation
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentDysonValue
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.InteractionVertexRelabel
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedPairContractionRegularity

set_option linter.style.header false

/-!
# Off-diagonal interaction-vertex covariance

Common owns interaction-slot relabeling of standard two-point diagrams, mixed-order positions,
pairings, and explicit component-shuffle slot permutations. This module starts at the fermionic field
realization and proves covariance of contractions, fixed-time amplitudes, and Dyson amplitudes.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

omit [LinearOrder Mode] [Fintype Mode] in
private theorem orderedTwoPointLegField_relabelInteractionVertices {n : ℕ}
    (π : Equiv.Perm (Fin n)) (i j : Mode) (τ τ' : ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ)
    (leg : OrderedTwoPointLeg n) :
    orderedTwoPointLegField i j τ τ' (fun v => q (π v)) σ leg =
      orderedTwoPointLegField i j τ τ' q (fun v => σ (π.symm v))
        (interactionVertexLegRelabel π leg) := by
  rcases leg with e | ⟨⟨v, hv⟩, l⟩
  · rfl
  · simp [orderedTwoPointLegField, orderedTwoPointLegTime,
      orderedTwoPointLegFieldLabel, interactionVertexLegRelabel]

omit [Fintype Mode] in
private theorem mixedTimeOrderedAtomicFieldFamily_relabelInteractionVertices_of_injective {n : ℕ}
    (π : Equiv.Perm (Fin n)) (ε : Mode → ℝ) (i j : Mode) (τ τ' : ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ)
    (hσ : Function.Injective σ) (p : Fin (2 * (2 * n + 1))) :
    mixedTimeOrderedAtomicFieldFamily ε i j τ τ' (fun v => q (π v)) σ p =
      mixedTimeOrderedAtomicFieldFamily ε i j τ τ' q (fun v => σ (π.symm v)) p := by
  rw [mixedTimeOrderedAtomicFieldFamily_eq_orderedTwoPointLegField,
    mixedTimeOrderedAtomicFieldFamily_eq_orderedTwoPointLegField]
  have hleg := mixedTimeOrderedAtomicLegEquiv_interactionVertexMixedPositionRelabel
    π τ τ' σ p
  rw [interactionVertexMixedPositionRelabel_apply_eq_of_injective π τ τ' σ hσ p] at hleg
  rw [hleg]
  exact orderedTwoPointLegField_relabelInteractionVertices π i j τ τ' q σ _

omit [Fintype Mode] in
private theorem mixedTimeOrderedAtomicOperatorFamily_relabelInteractionVertices_of_injective {n : ℕ}
    (π : Equiv.Perm (Fin n)) (ε : Mode → ℝ) (i j : Mode) (τ τ' : ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ)
    (hσ : Function.Injective σ) (p : Fin (2 * (2 * n + 1))) :
    mixedTimeOrderedAtomicOperatorFamily ε i j τ τ' (fun v => q (π v)) σ p =
      mixedTimeOrderedAtomicOperatorFamily ε i j τ τ' q (fun v => σ (π.symm v)) p := by
  change timedFieldOperator ε
      (mixedTimeOrderedAtomicFieldFamily ε i j τ τ' (fun v => q (π v)) σ p) =
    timedFieldOperator ε
      (mixedTimeOrderedAtomicFieldFamily ε i j τ τ' q (fun v => σ (π.symm v)) p)
  rw [mixedTimeOrderedAtomicFieldFamily_relabelInteractionVertices_of_injective
    π ε i j τ τ' q σ hσ p]

/-- Each density-state contraction is invariant under interaction-slot relabeling at injective
interaction times. -/
private theorem mixedTimeOrderedAtomicPairValue_relabelInteractionVertices_of_injective {n : ℕ}
    (π : Equiv.Perm (Fin n)) (ε : Mode → ℝ) (β : ℝ) (i j : Mode) (τ τ' : ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ)
    (hσ : Function.Injective σ) (a b : Fin (2 * (2 * n + 1))) :
    mixedTimeOrderedAtomicPairValue ε β i j τ τ' σ (fun v => q (π v)) a b =
      mixedTimeOrderedAtomicPairValue ε β i j τ τ' (fun v => σ (π.symm v)) q a b := by
  simp only [mixedTimeOrderedAtomicPairValue]
  rw [mixedTimeOrderedAtomicOperatorFamily_relabelInteractionVertices_of_injective
      π ε i j τ τ' q σ hσ a,
    mixedTimeOrderedAtomicOperatorFamily_relabelInteractionVertices_of_injective
      π ε i j τ τ' q σ hσ b]

/-- A complete mixed-order pairing value is invariant under interaction-slot relabeling at injective
interaction times. -/
private theorem orderedTwoPointPairingValue_relabelInteractionVertices_of_injective {n : ℕ}
    (π : Equiv.Perm (Fin n)) (ε : Mode → ℝ) (β : ℝ) (i j : Mode) (τ τ' : ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ)
    (hσ : Function.Injective σ) (pairing : Pairing (2 * n + 1)) :
    orderedTwoPointPairingValue ε β i j τ τ' σ (fun v => q (π v)) pairing =
      orderedTwoPointPairingValue ε β i j τ τ' (fun v => σ (π.symm v)) q pairing := by
  unfold orderedTwoPointPairingValue
  have hPairValue :
      mixedTimeOrderedAtomicPairValue ε β i j τ τ' σ (fun v => q (π v)) =
        mixedTimeOrderedAtomicPairValue ε β i j τ τ' (fun v => σ (π.symm v)) q := by
    funext a b
    exact mixedTimeOrderedAtomicPairValue_relabelInteractionVertices_of_injective
      π ε β i j τ τ' q σ hσ a b
  rw [hPairValue]

/-- The fixed-time amplitude is covariant under interaction-slot relabeling away from interaction-time
diagonals. -/
private theorem fixedTimeAmplitude_relabelInteractionVertices_of_injective
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (π : Equiv.Perm (Fin n)) (ε : Mode → ℝ) (β : ℝ)
    (g : QuarticVertexLabel Mode → ℂ) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hσ : Function.Injective σ) :
    (d.relabelInteractionVertices π).fixedTimeAmplitude ε β g τ τ' σ =
      d.fixedTimeAmplitude ε β g τ τ' (fun v => σ (π.symm v)) := by
  change twoPointExternalOrderSign τ τ' *
      orderedTwoPointVertexWeight g (d.relabelInteractionVertices π).vertexLabelSequence *
        orderedTwoPointPairingValue ε β i j τ τ' σ
          (d.relabelInteractionVertices π).vertexLabelSequence
          ((d.relabelInteractionVertices π).1.pairingInMixedOrder τ τ' σ) =
    twoPointExternalOrderSign τ τ' * orderedTwoPointVertexWeight g d.vertexLabelSequence *
      orderedTwoPointPairingValue ε β i j τ τ' (fun v => σ (π.symm v))
        d.vertexLabelSequence
        (d.1.pairingInMixedOrder τ τ' (fun v => σ (π.symm v)))
  rw [d.relabelInteractionVertices_vertexWeight g π]
  have hpairing :
      (d.relabelInteractionVertices π).1.pairingInMixedOrder τ τ' σ =
        d.1.pairingInMixedOrder τ τ' (fun v => σ (π.symm v)) := by
    change (d.1.relabelInteractionVertices π).pairingInMixedOrder τ τ' σ =
      d.1.pairingInMixedOrder τ τ' (fun v => σ (π.symm v))
    exact d.1.pairingInMixedOrder_relabelInteractionVertices_of_injective
      π τ τ' σ hσ
  rw [hpairing]
  have hq : (d.relabelInteractionVertices π).vertexLabelSequence =
      fun v => d.vertexLabelSequence (π v) := by
    funext v
    exact d.relabelInteractionVertices_vertexLabelSequence π v
  rw [hq]
  rw [orderedTwoPointPairingValue_relabelInteractionVertices_of_injective
    π ε β i j τ τ' d.vertexLabelSequence σ hσ
      (d.1.pairingInMixedOrder τ τ' (fun v => σ (π.symm v)))]

/-- The order-`n` Dyson-signed fixed-time amplitude inherits fixed-time interaction-slot relabeling
covariance. -/
theorem FixedExternalTwoPointWickDiagram.dysonFixedTimeAmplitude_relabelInteractionVertices_of_injective
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (π : Equiv.Perm (Fin n)) (ε : Mode → ℝ) (β : ℝ)
    (g : QuarticVertexLabel Mode → ℂ) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hσ : Function.Injective σ) :
    (d.relabelInteractionVertices π).dysonFixedTimeAmplitude ε β g τ τ' σ =
      d.dysonFixedTimeAmplitude ε β g τ τ' (fun v => σ (π.symm v)) := by
  unfold FixedExternalTwoPointWickDiagram.dysonFixedTimeAmplitude
  rw [fixedTimeAmplitude_relabelInteractionVertices_of_injective d π ε β g τ τ' σ hσ]

end Fermionic
end SecondQuantization
