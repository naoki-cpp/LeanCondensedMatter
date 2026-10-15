import LeanCondensedMatter.Combinatorics.FamilySlotShuffleSign
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Factorization.MixedComponentShuffle
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Factorization.ComponentShuffleParity
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Pairing.ComponentMixedPairEquiv
import LeanCondensedMatter.Combinatorics.PerfectPairing.ComponentCrossing
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.Diagram
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.ComponentSign

set_option linter.style.header false

/-!
# Mixed/fixed component shuffle signs for arbitrary external insertions

The canonical component decomposition gives two order-preserving family shuffles of the same atomic
legs: one in the fixed flattened order and one in mixed imaginary-time order. This file identifies
the sign of the relative permutation between those shuffles with the product of the fixed external
component regrouping sign and the residual mixed inter-component fermionic crossing sign.
-/

namespace SecondQuantization
namespace Fermionic

open Common Combinatorics
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


end Fermionic
end SecondQuantization
