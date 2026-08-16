import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ComponentShufflePermutation
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentMeasurability

set_option linter.style.header false

/-!
# Local interaction-time interface for two-point Dyson component factors

The generic dependent-slot API localizes every signed component factor to its interaction-time
fiber. Common owns the canonical conversion between finite-set ambient coordinates and explicit
`Fin n` slot coordinates. The complete locality statement is reduced to the mixed component pairing
value: the Dyson sign and quartic coupling product are independent of the interaction-time
assignment.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- Local interaction-time integrand obtained from one ambient signed component factor along a
chosen component interaction shuffle. -/
noncomputable def FixedExternalTwoPointWickDiagram.mixedComponentDysonLocalIntegrand
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (shuffle : d.1.ComponentInteractionShuffle)
    (B : d.1.componentPartition.parts) :
    (Fin (d.1.interactionComponentSize B) → ℝ) → ℂ :=
  DependentSlotEquiv.localize shuffle.slotEquiv B
    (fun σ => d.mixedComponentDysonFixedTimeValue ε β g τ τ'
      ((twoPointSlotTimeEquiv (n := n)) σ) B)

/-- Every canonical localized Dyson-signed component factor is globally measurable. The result is
obtained by composing the ambient finite-signature measurability theorem with the continuous
single-fiber coordinate embedding; it does not assert continuity across mixed-order walls. -/
theorem FixedExternalTwoPointWickDiagram.measurable_mixedComponentDysonLocalIntegrand
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (shuffle : d.1.ComponentInteractionShuffle)
    (B : d.1.componentPartition.parts) :
    Measurable (d.mixedComponentDysonLocalIntegrand ε β g τ τ' shuffle B) := by
  have hAmbient := d.measurable_mixedComponentDysonFixedTimeValue ε β g τ τ' B
  have hEmbed : Continuous (fun localTime : Fin (d.1.interactionComponentSize B) → ℝ =>
      (twoPointSlotTimeEquiv (n := n))
        (DependentSlotEquiv.ofAssignment shuffle.slotEquiv B localTime)) :=
    (continuous_pi fun i => continuous_apply ((twoPointSlotEquiv (n := n)) i)).comp
      (DependentSlotEquiv.continuous_ofAssignment shuffle.slotEquiv B)
  unfold FixedExternalTwoPointWickDiagram.mixedComponentDysonLocalIntegrand
  unfold DependentSlotEquiv.localize
  exact hAmbient.comp hEmbed.measurable

/-- Locality of the mixed component pairing value implies locality of the complete Dyson-signed
component factor, because its Dyson sign and coupling weight do not depend on interaction times. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentDysonFixedTimeValue_local_of_pairingValue_local
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (shuffle : d.1.ComponentInteractionShuffle)
    (B : d.1.componentPartition.parts)
    (hPairing : DependentSlotEquiv.Local shuffle.slotEquiv B
      (fun σ => d.mixedComponentPairingValue ε β τ τ'
        ((twoPointSlotTimeEquiv (n := n)) σ) B)) :
    DependentSlotEquiv.Local shuffle.slotEquiv B
      (fun σ => d.mixedComponentDysonFixedTimeValue ε β g τ τ'
        ((twoPointSlotTimeEquiv (n := n)) σ) B) := by
  intro σ υ hσυ
  unfold FixedExternalTwoPointWickDiagram.mixedComponentDysonFixedTimeValue
  unfold FixedExternalTwoPointWickDiagram.mixedComponentFixedTimeValue
  change d.mixedComponentDysonSign B *
      (d.mixedComponentVertexWeight g B *
        d.mixedComponentPairingValue ε β τ τ'
          ((twoPointSlotTimeEquiv (n := n)) σ) B) =
    d.mixedComponentDysonSign B *
      (d.mixedComponentVertexWeight g B *
        d.mixedComponentPairingValue ε β τ τ'
          ((twoPointSlotTimeEquiv (n := n)) υ) B)
  have hp :
      d.mixedComponentPairingValue ε β τ τ'
          ((twoPointSlotTimeEquiv (n := n)) σ) B =
        d.mixedComponentPairingValue ε β τ τ'
          ((twoPointSlotTimeEquiv (n := n)) υ) B :=
    hPairing σ υ hσυ
  rw [hp]

/-- Once every signed component factor is local along `shuffle`, the pointwise Dyson amplitude is the
external ordering sign times the corresponding component-shuffle integrand. -/
theorem FixedExternalTwoPointWickDiagram.dysonFixedTimeAmplitude_eq_externalSign_mul_componentShuffleIntegrand
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (shuffle : d.1.ComponentInteractionShuffle)
    (hLocal : ∀ B : d.1.componentPartition.parts,
      DependentSlotEquiv.Local shuffle.slotEquiv B
        (fun σ => d.mixedComponentDysonFixedTimeValue ε β g τ τ'
          ((twoPointSlotTimeEquiv (n := n)) σ) B))
    (σ : Fin n → ℝ) :
    d.dysonFixedTimeAmplitude ε β g τ τ' σ =
      twoPointExternalOrderSign τ τ' *
        d.1.interactionComponentShuffleIntegrand shuffle
          (d.mixedComponentDysonLocalIntegrand ε β g τ τ' shuffle)
          ((twoPointSlotTimeEquiv (n := n)).symm σ) := by
  rw [d.dysonFixedTimeAmplitude_eq_externalSign_mul_prod_components]
  apply congrArg (fun z : ℂ => twoPointExternalOrderSign τ τ' * z)
  let F : ∀ B : d.1.componentPartition.parts,
      (Fin (Finset.univ : Finset (Fin n)).card → ℝ) → ℂ :=
    fun B υ => d.mixedComponentDysonFixedTimeValue ε β g τ τ'
      ((twoPointSlotTimeEquiv (n := n)) υ) B
  calc
    (∏ B : d.1.componentPartition.parts,
        d.mixedComponentDysonFixedTimeValue ε β g τ τ' σ B) =
      ∏ B : d.1.componentPartition.parts,
        F B ((twoPointSlotTimeEquiv (n := n)).symm σ) := by
      apply Fintype.prod_congr
      intro B
      simp [F]
    _ = d.1.interactionComponentShuffleIntegrand shuffle
        (fun B => DependentSlotEquiv.localize shuffle.slotEquiv B (F B))
        ((twoPointSlotTimeEquiv (n := n)).symm σ) := by
      unfold SecondQuantization.Common.TwoPointDiagram.interactionComponentShuffleIntegrand
      apply Fintype.prod_congr
      intro B
      change F B ((twoPointSlotTimeEquiv (n := n)).symm σ) =
        DependentSlotEquiv.localize shuffle.slotEquiv B (F B)
          (DependentSlotEquiv.assignment shuffle.slotEquiv
            ((twoPointSlotTimeEquiv (n := n)).symm σ) B)
      exact DependentSlotEquiv.eq_localize shuffle.slotEquiv B (F B) (hLocal B)
        ((twoPointSlotTimeEquiv (n := n)).symm σ)
    _ = d.1.interactionComponentShuffleIntegrand shuffle
        (d.mixedComponentDysonLocalIntegrand ε β g τ τ' shuffle)
        ((twoPointSlotTimeEquiv (n := n)).symm σ) := by
      rfl

end Fermionic
end SecondQuantization
