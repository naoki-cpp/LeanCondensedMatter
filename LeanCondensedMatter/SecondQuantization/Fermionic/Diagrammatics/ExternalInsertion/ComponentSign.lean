import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Factorization.ComponentCrossing
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Factorization.ComponentShuffleParity

set_option linter.style.header false

/-!
# Fermionic external-component shuffle sign

For an external-insertion diagram, the Common layer reduces the residual inter-component pairing
crossing parity to the canonical shuffle of the odd external insertions. This file gives that
external shuffle its fermionic exchange sign and identifies the residual pairing weight with it.

The explicit component order is semantic input. A later time-ordering layer can supply that order
without changing the sign transport proved here.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open scoped BigOperators

variable {ExternalLabel InternalLabel : Type*} {E N : ℕ}

/-- Fermionic exchange sign for regrouping ambient external insertions into component blocks,
preserving the canonical increasing external order inside each component. -/
noncomputable def componentExternalOrderSign
    {S : Finset (Fin N)}
    (d : Common.ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (blockOrder :
      d.vertexGraph.componentPartition.parts ≃
        Fin (Fintype.card d.vertexGraph.componentPartition.parts)) : ℂ :=
  (Common.Statistics.fermion.zetaInt : ℂ) ^
    d.componentExternalShuffle.orderedBlockInversionCount blockOrder

/-- The residual inter-component fermionic pairing weight is exactly the exchange sign required to
regroup the odd external insertions by connected component. -/
theorem interComponentWeight_eq_componentExternalOrderSign
    {S : Finset (Fin N)}
    (d : Common.ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (blockOrder :
      d.vertexGraph.componentPartition.parts ≃
        Fin (Fintype.card d.vertexGraph.componentPartition.parts)) :
    (Common.Statistics.fermion.zetaInt : ℂ) ^ d.interComponentCrossingCount =
      componentExternalOrderSign d blockOrder := by
  unfold componentExternalOrderSign
  apply Common.BlochDeDominicis.zetaInt_pow_eq_of_mod_two_eq
  exact
    (d.interComponentCrossingCount_mod_two_eq_orderedBlockInversionCount blockOrder).trans
      (d.componentLegShuffle_orderedBlockInversionCount_mod_two_eq_external blockOrder)

/-- Fermionic pairing weight factorization for arbitrary external-insertion components: the only
global sign left after multiplying component-local pairing weights is the external-component order
sign. -/
theorem pairingWeight_eq_componentExternalOrderSign_mul_prod_components
    {S : Finset (Fin N)}
    (d : Common.ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (blockOrder :
      d.vertexGraph.componentPartition.parts ≃
        Fin (Fintype.card d.vertexGraph.componentPartition.parts)) :
    d.pairing.weight Common.Statistics.fermion =
      componentExternalOrderSign d blockOrder *
        ∏ B : d.vertexGraph.componentPartition.parts,
          (d.restrictComponent B).pairing.weight Common.Statistics.fermion := by
  rw [d.weight_eq_inter_mul_prod_components Common.Statistics.fermion,
    interComponentWeight_eq_componentExternalOrderSign d blockOrder]

end Fermionic
end SecondQuantization
