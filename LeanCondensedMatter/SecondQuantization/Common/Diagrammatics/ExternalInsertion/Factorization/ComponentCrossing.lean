import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Pairing.ComponentPairEquiv
import LeanCondensedMatter.Combinatorics.PerfectPairing.ComponentCrossing
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.PairingWeight

set_option linter.style.header false

/-!
# Crossing decomposition for external-insertion components

For a generic external-insertion diagram, component-internal crossings need not account for the
entire global crossing parity. Distinct connected components can interleave in the canonical ambient
leg order, so their crossings contribute an explicit residual inter-component term.

This module isolates that residual exactly. It does not assume the quartic-only parity cancellation.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*} {E N : ℕ}

/-- Total oriented crossing count between distinct connected components of an external-insertion
diagram. -/
noncomputable def ExternalInsertionDiagram.interComponentCrossingCount
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S) : ℕ :=
  d.pairing.interComponentCrossingCount d.componentPairEquiv


/-- Number of ambient leg-order inversions from component `C` across component `B`.
This is the generic block-inversion count of the canonical component-leg shuffle. -/
noncomputable def ExternalInsertionDiagram.componentLegInversionCount
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B C : d.vertexGraph.componentPartition.parts) : ℕ :=
  d.componentLegShuffle.blockInversionCount B C

/-- For distinct components, the parity of the two oriented crossing counts is exactly the parity
of the canonical ambient leg inversions between those components. -/
theorem ExternalInsertionDiagram.componentCrossingCount_add_swap_mod_two_eq_legInversionCount
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B C : d.vertexGraph.componentPartition.parts) (hBC : B ≠ C) :
    (d.pairing.componentCrossingCount d.componentPairEquiv B C +
      d.pairing.componentCrossingCount d.componentPairEquiv C B) % 2 =
      d.componentLegInversionCount B C % 2 := by
  rw [← d.pairing.componentGeometricCrossingCount_eq_oriented_add d.componentPairEquiv B C,
    ExternalInsertionDiagram.componentLegInversionCount,
    d.componentLegShuffle.blockInversionCount_of_ne hBC]
  simp only [ExternalInsertionDiagram.componentLegShuffle_slotEquiv_apply]
  exact d.pairing.componentGeometricCrossingCount_mod_two_eq_endpointInversionCount
    d.componentPairEquiv
    (fun D => (d.restrictComponent D).pairing.pairEndpointEquiv)
    (fun D p => d.componentDiagramLeg D p)
    (fun D p k => by
      fin_cases k <;>
        simp [Combinatorics.Pairing.pairEndpointEquiv_apply,
          Combinatorics.Pairing.pairEndpoint, Combinatorics.pairEndpointAt,
          d.componentPairEquiv_apply])
    B C hBC

/-- The residual inter-component crossing parity is the total block-inversion parity of the
canonical component-leg shuffle, relative to any explicit ordering of the connected components. -/
theorem ExternalInsertionDiagram.interComponentCrossingCount_mod_two_eq_orderedBlockInversionCount
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (blockOrder :
      d.vertexGraph.componentPartition.parts ≃ Fin (Fintype.card d.vertexGraph.componentPartition.parts)) :
    d.interComponentCrossingCount % 2 =
      d.componentLegShuffle.orderedBlockInversionCount blockOrder % 2 := by
  classical
  let cross := fun B C : d.vertexGraph.componentPartition.parts =>
    d.pairing.componentCrossingCount d.componentPairEquiv B C
  let inv := fun B C : d.vertexGraph.componentPartition.parts =>
    d.componentLegInversionCount B C
  let selected := fun B C : d.vertexGraph.componentPartition.parts =>
    if blockOrder B < blockOrder C then inv B C else 0
  have hsum :=
    finset_sum_offDiag_modEq_of_pair_add_modEq
      2 (Finset.univ : Finset d.vertexGraph.componentPartition.parts) cross selected
      (fun B _ C _ hBC => by
        by_cases hlt : blockOrder B < blockOrder C
        · have hnlt : ¬ blockOrder C < blockOrder B := asymm hlt
          simpa [Nat.ModEq, selected, hlt, hnlt, inv, cross] using
            d.componentCrossingCount_add_swap_mod_two_eq_legInversionCount B C hBC
        · have hneOrder : blockOrder B ≠ blockOrder C := by
            intro h
            exact hBC (blockOrder.injective h)
          have hrev : blockOrder C < blockOrder B := by
            rcases lt_trichotomy (blockOrder B) (blockOrder C) with h | h | h
            · exact absurd h hlt
            · exact absurd h hneOrder
            · exact h
          simpa [Nat.ModEq, selected, hlt, hrev, inv, cross, add_comm] using
            d.componentCrossingCount_add_swap_mod_two_eq_legInversionCount C B hBC.symm)
  simpa [Nat.ModEq, ExternalInsertionDiagram.interComponentCrossingCount,
    Combinatorics.Pairing.interComponentCrossingCount,
    FamilySlotShuffleTo.orderedBlockInversionCount,
    ExternalInsertionDiagram.componentLegInversionCount,
    cross, inv, selected] using hsum

private theorem ExternalInsertionDiagram.componentCrossingCount_self
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.vertexGraph.componentPartition.parts) :
    d.pairing.componentCrossingCount d.componentPairEquiv B B =
      (d.restrictComponent B).pairing.crossingCount := by
  exact Combinatorics.Pairing.componentCrossingCount_self_eq
    d.pairing (d.restrictComponent B).pairing d.componentPairEquiv B
    (Equiv.refl (d.restrictComponent B).pairing.NormalizedPair)
    (d.componentDiagramLeg B)
    (d.componentDiagramLegOrderEmbedding B).strictMono
    (fun pr => by simpa using d.componentPairEquiv_apply B pr)

/-- The ambient crossing count is the sum of all component-local crossing counts plus the residual
crossing count between distinct connected components. -/
theorem ExternalInsertionDiagram.crossingCount_eq_sum_components_add_inter
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S) :
    d.pairing.crossingCount =
      (∑ B : d.vertexGraph.componentPartition.parts, (d.restrictComponent B).pairing.crossingCount) +
        d.interComponentCrossingCount := by
  rw [d.pairing.crossingCount_eq_sum_componentCrossingCount_diag_add_inter d.componentPairEquiv]
  apply congrArg (fun n : ℕ => n + d.interComponentCrossingCount)
  apply Finset.sum_congr rfl
  intro B _
  exact d.componentCrossingCount_self B

/-- The exchange-statistics weight factors into the residual inter-component exchange sign and the
product of component-local pairing weights. -/
theorem ExternalInsertionDiagram.weight_eq_inter_mul_prod_components
    (s : Statistics) {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S) :
    d.pairing.weight s =
      (s.zetaInt : ℂ) ^ d.interComponentCrossingCount *
        ∏ B : d.vertexGraph.componentPartition.parts, (d.restrictComponent B).pairing.weight s := by
  classical
  simp only [Combinatorics.Pairing.weight]
  rw [d.crossingCount_eq_sum_components_add_inter, pow_add,
    ← Finset.prod_pow_eq_pow_sum]
  exact mul_comm _ _

end Common
end SecondQuantization
