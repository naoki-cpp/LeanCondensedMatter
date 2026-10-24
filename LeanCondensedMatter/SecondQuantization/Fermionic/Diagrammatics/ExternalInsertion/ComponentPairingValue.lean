import LeanCondensedMatter.Combinatorics.Shuffle.FamilySlotShuffleSign
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Factorization.MixedComponentShuffle
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Factorization.ComponentShuffleParity
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Pairing.ComponentMixedPairEquiv
import LeanCondensedMatter.Combinatorics.PerfectPairing.ComponentCrossing
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.Diagram
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.ComponentSign
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.PairingWeight
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.ComponentPairingLocality

set_option linter.style.header false

/-!
# Component factorization of arbitrary-external mixed pair contractions

The mixed-order component pair equivalence identifies every ambient normalized pair with exactly one
component-local normalized pair. The concrete free-Gibbs pair kernel is local under the corresponding
mixed-position embedding. The canonical `Pairing.evaluation_eq_mul_prod_components` theorem then
factors the mixed pairing value into its inter-component exchange sign and local evaluations.
The relative fixed/mixed component shuffle sign then cancels the inter-component exchange sign
when forming the componentwise pairing factorization.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Common
open scoped BigOperators

variable {Mode : Type*}

/-- The relative permutation between fixed and mixed component shuffles carries exactly the fixed
external regrouping sign and the residual mixed inter-component crossing sign. -/
theorem ExternalInsertionWickDiagram.relativeComponentShuffleSign_eq_external_mul_mixedInter
    {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (blockOrder : d.vertexGraph.componentPartition.parts ≃
      Fin (Fintype.card d.vertexGraph.componentPartition.parts)) :
    (((Equiv.Perm.sign (d.relativeComponentShuffle externalTime σ) : ℤ) : ℂ)) =
      componentExternalOrderSign d blockOrder *
        (Common.Statistics.fermion.zetaInt : ℂ) ^
          (d.pairingInMixedOrder externalTime σ).interComponentCrossingCount
          (d.componentMixedPairEquiv externalTime σ) := by
  let fixedShuffle :=
    FamilySlotShuffleTo.castTotalEquiv
      (m := 2 * (2 * (Finset.univ : Finset (Fin n)).card + E))
      (n := 2 * (2 * n + E)) (by simp) d.componentLegShuffle
  change (((Equiv.Perm.sign
    (fixedShuffle.relativePerm
      (d.componentMixedPositionShuffle externalTime σ)) : ℤ) : ℂ)) = _
  rw [FamilySlotShuffleTo.relativePerm_sign_eq_orderedBlockInversionCount_add
    fixedShuffle (d.componentMixedPositionShuffle externalTime σ) blockOrder]
  simp only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one,
    Int.cast_pow, Int.cast_neg, Int.cast_one]
  rw [pow_add]
  unfold componentExternalOrderSign
  have hfixed :
      fixedShuffle.orderedBlockInversionCount blockOrder % 2 =
        d.componentExternalShuffle.orderedBlockInversionCount blockOrder % 2 := by
    change d.componentLegShuffle.orderedBlockInversionCount blockOrder % 2 =
      d.componentExternalShuffle.orderedBlockInversionCount blockOrder % 2
    exact d.componentLegShuffle_orderedBlockInversionCount_mod_two_eq_external blockOrder
  have hmixed :=
    Pairing.interComponentCrossingCount_mod_two_eq_orderedBlockInversionCount
      (d.pairingInMixedOrder externalTime σ)
      (d.componentMixedPairEquiv externalTime σ)
      (fun B =>
        ((d.componentOrderedDiagram B).pairingInMixedOrder
          (d.componentExternalTime externalTime B)
          (d.componentInteractionTime σ B)).pairEndpointEquiv)
      (d.componentMixedPositionShuffle externalTime σ)
      (fun B p k => by
        fin_cases k <;>
          simp [ExternalInsertionDiagram.componentMixedPositionShuffle_slotEquiv_apply,
            Pairing.pairEndpointEquiv_apply, Pairing.pairEndpoint, pairEndpointAt,
            d.componentMixedPairEquiv_apply externalTime σ])
      blockOrder
  rw [pow_eq_of_mod_two_eq (show ((-1 : ℂ) * -1) = 1 by norm_num) hfixed]
  rw [pow_eq_of_mod_two_eq (show ((-1 : ℂ) * -1) = 1 by norm_num) hmixed.symm]
  simp only [Common.Statistics.zetaInt_fermion, Int.cast_neg, Int.cast_one]

variable [LinearOrder Mode] [Fintype Mode]

/-- The concrete mixed pairing evaluation factors into the residual mixed inter-component fermionic
sign and the standalone mixed pairing values of all connected components. -/
theorem ExternalInsertionWickDiagram.mixedPairingValue_eq_inter_mul_prod_components
    {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
    (ε : Mode → ℝ) (β : ℝ)
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    d.mixedPairingValue ε β externalTime σ =
      (Common.Statistics.fermion.zetaInt : ℂ) ^
        (d.pairingInMixedOrder externalTime σ).interComponentCrossingCount
          (d.componentMixedPairEquiv externalTime σ) *
      ∏ B : d.vertexGraph.componentPartition.parts,
        ExternalInsertionWickDiagram.mixedPairingValue (d.componentOrderedDiagram B) ε β
          (d.componentExternalTime externalTime B)
          (d.componentInteractionTime σ B) := by
  let pairing := d.pairingInMixedOrder externalTime σ
  let localPairing := fun B : d.vertexGraph.componentPartition.parts =>
    (d.componentOrderedDiagram B).pairingInMixedOrder
      (d.componentExternalTime externalTime B)
      (d.componentInteractionTime σ B)
  let pairValue :=
    externalInsertionMixedTimeOrderedAtomicPairValue ε β
      d.externalLabel externalTime d.vertexLabelSequence σ
  let localPairValue := fun B : d.vertexGraph.componentPartition.parts =>
    externalInsertionMixedTimeOrderedAtomicPairValue ε β
      (d.componentOrderedDiagram B).externalLabel
      (d.componentExternalTime externalTime B)
      (d.componentOrderedDiagram B).vertexLabelSequence
      (d.componentInteractionTime σ B)
  change pairing.evaluation (pairing.weight Common.Statistics.fermion) pairValue =
    (Common.Statistics.fermion.zetaInt : ℂ) ^
      pairing.interComponentCrossingCount (d.componentMixedPairEquiv externalTime σ) *
    ∏ B, (localPairing B).evaluation
      ((localPairing B).weight Common.Statistics.fermion) (localPairValue B)
  exact Pairing.evaluation_eq_mul_prod_components
    pairing localPairing (d.componentMixedPairEquiv externalTime σ)
    (pairing.weight Common.Statistics.fermion)
    ((Common.Statistics.fermion.zetaInt : ℂ) ^
      pairing.interComponentCrossingCount (d.componentMixedPairEquiv externalTime σ))
    (fun B => (localPairing B).weight Common.Statistics.fermion)
    pairValue localPairValue
    (BlochDeDominicis.Pairing.weight_eq_inter_mul_prod_of_crossingCount_eq
      Common.Statistics.fermion pairing localPairing
      (pairing.interComponentCrossingCount (d.componentMixedPairEquiv externalTime σ))
      (Pairing.crossingCount_eq_sum_localCrossingCount_add_inter
        pairing localPairing (d.componentMixedPairEquiv externalTime σ)
        (fun B => Equiv.refl _)
        (fun B => d.componentMixedPosition externalTime σ B)
        (fun B => d.componentMixedPosition_strictMono externalTime σ B)
        (fun B pr => by
          exact d.componentMixedPairEquiv_apply externalTime σ B pr)))
    (fun B pr => by
      rw [d.componentMixedPairEquiv_apply externalTime σ B pr]
      exact d.externalInsertionMixedTimeOrderedAtomicPairValue_componentMixedPosition
        ε β externalTime σ B pr.1.1 pr.1.2)

/-- Multiplying the mixed pairing value by the sign that carries fixed component-leg order to
mixed-time component-leg order leaves the fixed external-component sign times the component-local
mixed pairing values. This is a pairing-level identity; it does not assert factorization of the
full fixed-time amplitude. -/
theorem ExternalInsertionWickDiagram.relativeComponentShuffleSign_mul_mixedPairingValue_eq_componentExternalOrderSign_mul_prod_components
    {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
    (ε : Mode → ℝ) (β : ℝ)
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (blockOrder : d.vertexGraph.componentPartition.parts ≃
      Fin (Fintype.card d.vertexGraph.componentPartition.parts)) :
    (((Equiv.Perm.sign (d.relativeComponentShuffle externalTime σ) : ℤ) : ℂ)) *
        d.mixedPairingValue ε β externalTime σ =
      componentExternalOrderSign d blockOrder *
        ∏ B : d.vertexGraph.componentPartition.parts,
          ExternalInsertionWickDiagram.mixedPairingValue (d.componentOrderedDiagram B) ε β
            (d.componentExternalTime externalTime B)
            (d.componentInteractionTime σ B) := by
  conv_lhs =>
    rw [d.relativeComponentShuffleSign_eq_external_mul_mixedInter
      (blockOrder := blockOrder)]
    rw [d.mixedPairingValue_eq_inter_mul_prod_components]
  set interCount :=
    (d.pairingInMixedOrder externalTime σ).interComponentCrossingCount
      (d.componentMixedPairEquiv externalTime σ)
  calc
    _ = componentExternalOrderSign d blockOrder *
          (((Common.Statistics.fermion.zetaInt : ℂ) ^
                interCount *
              (Common.Statistics.fermion.zetaInt : ℂ) ^
                interCount) *
            ∏ B : d.vertexGraph.componentPartition.parts,
              ExternalInsertionWickDiagram.mixedPairingValue (d.componentOrderedDiagram B) ε β
                (d.componentExternalTime externalTime B)
                (d.componentInteractionTime σ B)) := by
      ac_rfl
    _ = _ := by
      simp [Common.Statistics.zetaInt_fermion, ← mul_pow]

end Fermionic
end SecondQuantization
