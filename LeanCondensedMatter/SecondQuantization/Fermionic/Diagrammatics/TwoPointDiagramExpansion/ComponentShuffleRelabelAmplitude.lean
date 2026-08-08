import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.ComponentShufflePermutation
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.InteractionVertexRelabelFixedTimeAmplitude

set_option linter.style.header false

/-!
# Component-shuffle terms as relabeled fixed-diagram amplitudes

The component-shuffle layer already expresses each shuffled localized product as the original
fixed diagram's Dyson fixed-time amplitude at a permuted interaction-time assignment.  The
interaction-vertex covariance theorem identifies that permuted value with the amplitude of the
correspondingly relabeled diagram at the unpermuted assignment, away from interaction-time
diagonals.

This is the pointwise bridge needed before reindexing the total finite fixed-diagram sum.  No
per-diagram orbit or stabilizer argument is introduced.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

omit [LinearOrder Mode] [Fintype Mode] in
/-- Injectivity of an ambient interaction-time assignment is preserved when transporting it to the
explicit `Fin n` interaction-slot type. -/
theorem ambientToTwoPointSlotTimePermutation_injective {n : ℕ}
    {σ : Fin (Finset.univ : Finset (Fin n)).card → ℝ}
    (hσ : Function.Injective σ) :
    Function.Injective (ambientToTwoPointSlotTimePermutation σ) := by
  intro a b hab
  apply Fin.ext
  exact congrArg Fin.val (hσ hab)

/-- The order-`n` Dyson-signed fixed-time amplitude inherits the fixed-time interaction-slot
relabeling covariance. -/
theorem FixedExternalTwoPointWickDiagram.dysonFixedTimeAmplitude_relabelInteractionVertices_of_injective
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (π : Equiv.Perm (Fin n)) (ε : Mode → ℝ) (β : ℝ)
    (g : QuarticVertexLabel Mode → ℂ) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hσ : Function.Injective σ) :
    (d.relabelInteractionVertices π).dysonFixedTimeAmplitude ε β g τ τ' σ =
      d.dysonFixedTimeAmplitude ε β g τ τ' (fun v => σ (π.symm v)) := by
  unfold FixedExternalTwoPointWickDiagram.dysonFixedTimeAmplitude
  rw [d.fixedTimeAmplitude_relabelInteractionVertices_of_injective
    π ε β g τ τ' σ hσ]

/-- Away from interaction-time diagonals, one component-shuffle term is exactly the Dyson
fixed-time amplitude of the explicitly relabeled fixed diagram, evaluated at the original ambient
interaction times. -/
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
