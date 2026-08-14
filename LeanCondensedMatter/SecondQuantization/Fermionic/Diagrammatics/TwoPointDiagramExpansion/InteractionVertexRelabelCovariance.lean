import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.ComponentShufflePermutation
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.MixedOrderPairing
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.TwoPointInteractionRelabelMixedPosition
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedPairContractionRegularity

set_option linter.style.header false

/-!
# Off-diagonal interaction-vertex covariance

Interaction-slot relabeling is proved only at injective interaction-time assignments. Common owns
the mixed-order pairing and standard-position transport; this module adds fermionic field,
contraction, fixed-time amplitude, and Dyson-amplitude covariance.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

omit [LinearOrder Mode] [Fintype Mode] in
theorem twoPointLegEquiv_interactionVertexPositionRelabel {n : ℕ}
    (π : Equiv.Perm (Fin n))
    (p : Fin (2 * (2 * (Finset.univ : Finset (Fin n)).card + 1))) :
    Common.twoPointLegEquiv (Finset.univ : Finset (Fin n))
        (interactionVertexPositionRelabel π p) =
      interactionVertexLegRelabel π
        (Common.twoPointLegEquiv (Finset.univ : Finset (Fin n)) p) := by
  change
    Common.twoPointLegEquiv (Finset.univ : Finset (Fin n))
        ((Common.twoPointLegEquiv (Finset.univ : Finset (Fin n))).symm
          (interactionVertexLegRelabel π
            (Common.twoPointLegEquiv (Finset.univ : Finset (Fin n)) p))) =
      interactionVertexLegRelabel π
        (Common.twoPointLegEquiv (Finset.univ : Finset (Fin n)) p)
  exact (Common.twoPointLegEquiv (Finset.univ : Finset (Fin n))).apply_symm_apply _

omit [LinearOrder Mode] [Fintype Mode] in
theorem interactionVertexPositionRelabel_mixedTimeAmbientPositionEquiv_of_injective {n : ℕ}
    (π : Equiv.Perm (Fin n)) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hσ : Function.Injective σ) (p : Fin (2 * (2 * n + 1))) :
    interactionVertexPositionRelabel π (mixedTimeAmbientPositionEquiv τ τ' σ p) =
      mixedTimeAmbientPositionEquiv τ τ' (fun v => σ (π.symm v)) p := by
  apply (Common.twoPointLegEquiv (Finset.univ : Finset (Fin n))).injective
  rw [twoPointLegEquiv_interactionVertexPositionRelabel,
    twoPointLegEquiv_mixedTimeAmbientPositionEquiv,
    twoPointLegEquiv_mixedTimeAmbientPositionEquiv]
  have h := mixedTimeOrderedAtomicLegEquiv_interactionVertexMixedPositionRelabel
    π τ τ' σ p
  rw [interactionVertexMixedPositionRelabel_apply_eq_of_injective π τ τ' σ hσ p] at h
  exact h.symm

omit [LinearOrder Mode] [Fintype Mode] in
/-- Under injective interaction times, interaction-vertex relabeling commutes with the Common mixed
pairing. -/
theorem FixedExternalTwoPointWickDiagram.pairingInMixedOrder_relabelInteractionVertices_of_injective
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (π : Equiv.Perm (Fin n)) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hσ : Function.Injective σ) :
    (d.relabelInteractionVertices π).1.pairingInMixedOrder τ τ' σ =
      d.1.pairingInMixedOrder τ τ' (fun v => σ (π.symm v)) := by
  apply Pairing.ext
  apply Equiv.ext
  intro p
  apply (mixedTimeAmbientPositionEquiv τ τ' (fun v => σ (π.symm v))).injective
  calc
    mixedTimeAmbientPositionEquiv τ τ' (fun v => σ (π.symm v))
        (((d.relabelInteractionVertices π).1.pairingInMixedOrder τ τ' σ).partner p) =
      interactionVertexPositionRelabel π
        (mixedTimeAmbientPositionEquiv τ τ' σ
          (((d.relabelInteractionVertices π).1.pairingInMixedOrder τ τ' σ).partner p)) := by
        symm
        exact interactionVertexPositionRelabel_mixedTimeAmbientPositionEquiv_of_injective
          π τ τ' σ hσ _
    _ = interactionVertexPositionRelabel π
        ((d.relabelInteractionVertices π).1.pairing.partner
          (mixedTimeAmbientPositionEquiv τ τ' σ p)) := by
        rw [(d.relabelInteractionVertices π).1.mixedTimeAmbientPositionEquiv_partner]
    _ = d.1.pairing.partner
        (interactionVertexPositionRelabel π
          (mixedTimeAmbientPositionEquiv τ τ' σ p)) := by
        rw [FixedExternalTwoPointWickDiagram.relabelInteractionVertices_pairing,
          Pairing.relabel_partner]
        exact (interactionVertexPositionRelabel π).apply_symm_apply _
    _ = d.1.pairing.partner
        (mixedTimeAmbientPositionEquiv τ τ' (fun v => σ (π.symm v)) p) := by
        rw [interactionVertexPositionRelabel_mixedTimeAmbientPositionEquiv_of_injective
          π τ τ' σ hσ p]
    _ = mixedTimeAmbientPositionEquiv τ τ' (fun v => σ (π.symm v))
        ((d.1.pairingInMixedOrder τ τ' (fun v => σ (π.symm v))).partner p) := by
        symm
        exact d.1.mixedTimeAmbientPositionEquiv_partner
          τ τ' (fun v => σ (π.symm v)) p

omit [LinearOrder Mode] [Fintype Mode] in
theorem orderedTwoPointLegField_relabelInteractionVertices {n : ℕ}
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
theorem mixedTimeOrderedAtomicFieldFamily_relabelInteractionVertices_of_injective {n : ℕ}
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
theorem mixedTimeOrderedAtomicOperatorFamily_relabelInteractionVertices_of_injective {n : ℕ}
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
theorem mixedTimeOrderedAtomicPairValue_relabelInteractionVertices_of_injective {n : ℕ}
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
theorem orderedTwoPointPairingValue_relabelInteractionVertices_of_injective {n : ℕ}
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
theorem FixedExternalTwoPointWickDiagram.fixedTimeAmplitude_relabelInteractionVertices_of_injective
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
  rw [d.pairingInMixedOrder_relabelInteractionVertices_of_injective π τ τ' σ hσ]
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
  rw [d.fixedTimeAmplitude_relabelInteractionVertices_of_injective π ε β g τ τ' σ hσ]

omit [LinearOrder Mode] [Fintype Mode] in
theorem ambientToTwoPointSlotTimePermutation_injective {n : ℕ}
    {σ : Fin (Finset.univ : Finset (Fin n)).card → ℝ}
    (hσ : Function.Injective σ) :
    Function.Injective (ambientToTwoPointSlotTimePermutation σ) := by
  intro a b hab
  apply Fin.ext
  have hcast := hσ hab
  exact congrArg (fun x : Fin (Finset.univ : Finset (Fin n)).card => x.val) hcast

/-- Away from interaction-time diagonals, one component-shuffle term is exactly the Dyson fixed-time
amplitude of the explicitly relabeled diagram at the original ambient times. -/
theorem FixedExternalTwoPointWickDiagram.externalSign_mul_componentShuffleIntegrand_eq_relabelForComponentShuffle_dysonFixedTimeAmplitude_of_injective
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (shuffle : d.1.ComponentInteractionShuffle)
    (σ : Fin (Finset.univ : Finset (Fin n)).card → ℝ)
    (hσ : Function.Injective σ) :
    twoPointExternalOrderSign τ τ' *
        d.1.interactionComponentShuffleIntegrand shuffle
          (d.mixedComponentDysonLocalIntegrand ε β g τ τ'
            d.1.canonicalComponentInteractionShuffle) σ =
      (d.relabelForComponentShuffle shuffle).dysonFixedTimeAmplitude ε β g τ τ'
        (ambientToTwoPointSlotTimePermutation σ) := by
  rw [d.externalSign_mul_componentShuffleIntegrand_eq_dysonFixedTimeAmplitude_slotPermuted
    ε β g τ τ' shuffle σ]
  symm
  have hslot : Function.Injective (ambientToTwoPointSlotTimePermutation σ) :=
    ambientToTwoPointSlotTimePermutation_injective hσ
  simpa [FixedExternalTwoPointWickDiagram.relabelForComponentShuffle] using
    (d.dysonFixedTimeAmplitude_relabelInteractionVertices_of_injective
      (d.componentShuffleSlotPermutation shuffle).symm ε β g τ τ'
      (ambientToTwoPointSlotTimePermutation σ) hslot)

end Fermionic
end SecondQuantization
