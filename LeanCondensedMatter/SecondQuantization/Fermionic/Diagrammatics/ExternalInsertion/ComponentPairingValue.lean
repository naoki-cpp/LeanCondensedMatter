import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Factorization.MixedComponentCrossing
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.ComponentPairingLocality
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.ComponentOrderSign
import LeanCondensedMatter.Combinatorics.PerfectPairing.ComponentCrossing

set_option linter.style.header false

/-!
# Component factorization of arbitrary-external mixed pair contractions

The mixed-order component pair equivalence identifies every ambient normalized pair with exactly one
component-local normalized pair. The concrete free-Gibbs pair kernel is local under the corresponding
mixed-position embedding. The canonical `Pairing.evaluation_eq_mul_prod_components` theorem then
factors the mixed pairing value into its inter-component exchange sign and local evaluations.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Common
open scoped BigOperators

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

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
    (d.pairingInMixedOrder_weight_eq_inter_mul_prod_components
      Common.Statistics.fermion externalTime σ)
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
  have hsignsquare :
      (Common.Statistics.fermion.zetaInt : ℂ) ^
          d.mixedInterComponentCrossingCount externalTime σ *
        (Common.Statistics.fermion.zetaInt : ℂ) ^
          d.mixedInterComponentCrossingCount externalTime σ = 1 := by
    simp only [Common.Statistics.zetaInt_fermion, Int.cast_neg, Int.cast_one]
    rw [← mul_pow]
    norm_num
  calc
    _ = componentExternalOrderSign d blockOrder *
          (((Common.Statistics.fermion.zetaInt : ℂ) ^
                d.mixedInterComponentCrossingCount externalTime σ *
              (Common.Statistics.fermion.zetaInt : ℂ) ^
                d.mixedInterComponentCrossingCount externalTime σ) *
            ∏ B : d.vertexGraph.componentPartition.parts,
              ExternalInsertionWickDiagram.mixedPairingValue (d.componentOrderedDiagram B) ε β
                (d.componentExternalTime externalTime B)
                (d.componentInteractionTime σ B)) := by
      ac_rfl
    _ = _ := by rw [hsignsquare, one_mul]

end Fermionic
end SecondQuantization
