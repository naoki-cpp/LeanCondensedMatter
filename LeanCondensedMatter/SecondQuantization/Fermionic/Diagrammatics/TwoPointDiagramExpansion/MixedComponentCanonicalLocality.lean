import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ComponentShufflePermutation
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.MixedComponentTimeTransport
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentContractionTimeLocality
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentLocalTime

set_option linter.style.header false

/-!
# Canonical component locality for the two-point Dyson integrand

The canonical component shuffle assigns each local interaction slot to the rank of the corresponding
ambient interaction vertex. The crossing- and contraction-locality theorems then make the fermionic
component pairing value local without caller-supplied transport hypotheses and expose the pointwise
Dyson amplitude as the canonical component-shuffle integrand.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- The pointwise Dyson-signed two-point amplitude is the canonical component-shuffle integrand,
with no caller-supplied crossing or contraction preservation hypotheses. -/
theorem FixedExternalTwoPointWickDiagram.dysonFixedTimeAmplitude_eq_canonicalComponentShuffleIntegrand
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    d.dysonFixedTimeAmplitude ε β g τ τ' σ =
      twoPointExternalOrderSign τ τ' *
        d.1.interactionComponentShuffleIntegrand
          d.1.canonicalComponentInteractionShuffle
          (d.mixedComponentDysonLocalIntegrand ε β g τ τ'
            d.1.canonicalComponentInteractionShuffle)
          ((twoPointSlotTimeEquiv (n := n)).symm σ) := by
  apply d.dysonFixedTimeAmplitude_eq_externalSign_mul_componentShuffleIntegrand
    ε β g τ τ' d.1.canonicalComponentInteractionShuffle
  intro B
  apply d.mixedComponentDysonFixedTimeValue_local_of_pairingValue_local
    ε β g τ τ' d.1.canonicalComponentInteractionShuffle B
  intro σ υ hσυ
  apply d.mixedComponentPairingValue_eq_of_componentTimeEq
    ε β τ τ'
    ((twoPointSlotTimeEquiv (n := n)) σ)
    ((twoPointSlotTimeEquiv (n := n)) υ) B
  have hRestricted :
      d.1.interactionComponentTimeAssignment
          d.1.canonicalComponentInteractionShuffle σ B =
        d.1.interactionComponentTimeAssignment
          d.1.canonicalComponentInteractionShuffle υ B :=
    hσυ
  have hVertices :
      ∀ v : ↥(Common.TwoPointDiagram.interactionPart
        (B : Finset (Common.TwoPointVertex (Finset.univ : Finset (Fin n))))),
        (twoPointSlotTimeEquiv (n := n)) σ v.1 =
          (twoPointSlotTimeEquiv (n := n)) υ v.1 := by
    apply (d.1.canonicalComponentTimeAssignment_univ_eq_iff
      ((twoPointSlotTimeEquiv (n := n)) σ)
      ((twoPointSlotTimeEquiv (n := n)) υ) B).mp
    change d.1.interactionComponentTimeAssignment
        d.1.canonicalComponentInteractionShuffle
        ((twoPointSlotTimeEquiv (n := n)).symm
          ((twoPointSlotTimeEquiv (n := n)) σ)) B =
      d.1.interactionComponentTimeAssignment
        d.1.canonicalComponentInteractionShuffle
        ((twoPointSlotTimeEquiv (n := n)).symm
          ((twoPointSlotTimeEquiv (n := n)) υ)) B
    rw [(twoPointSlotTimeEquiv (n := n)).symm_apply_apply σ,
      (twoPointSlotTimeEquiv (n := n)).symm_apply_apply υ]
    exact hRestricted
  intro v hv
  exact hVertices ⟨v, hv⟩

end Fermionic
end SecondQuantization
