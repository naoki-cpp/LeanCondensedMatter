import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.ComponentData
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Factorization.ComponentCrossing
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.PairingWeight

set_option linter.style.header false

/-!
# Mixed-order component crossing factorization

The component-local mixed positions form an order-preserving family shuffle into the ambient
mixed-time atomic order. Reusing the generic perfect-pairing component-crossing API then splits the
ambient mixed crossing count into component-local crossing counts and one residual inter-component
term.

This layer is still statistics-independent except for the final reusable pairing-weight corollary.
The relation between the residual mixed block inversions and fermionic time-order permutation signs
is intentionally left downstream.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Common
open scoped BigOperators

variable {Mode : Type*}

/-- The canonical family shuffle from component-local mixed atomic positions to the ambient
mixed-time atomic positions. -/
noncomputable def ExternalInsertionWickDiagram.componentMixedPositionShuffle
    {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    FamilySlotShuffleTo
      (fun B : d.vertexGraph.componentPartition.parts =>
        2 * (2 * (interactionSector
          (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))).card +
            d.externalPairCount B))
      (2 * (2 * n + E)) where
  slotEquiv := d.componentMixedPositionEquiv externalTime σ
  strictMono := fun B => by
    intro a b hab
    simpa only [ExternalInsertionWickDiagram.componentMixedPositionEquiv_apply] using
      d.componentMixedPosition_strictMono externalTime σ B hab

@[simp]
theorem ExternalInsertionWickDiagram.componentMixedPositionShuffle_slotEquiv_apply
    {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (B : d.vertexGraph.componentPartition.parts)
    (p : Fin (2 * (2 * (interactionSector
      (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))).card +
        d.externalPairCount B))) :
    (d.componentMixedPositionShuffle externalTime σ).slotEquiv ⟨B, p⟩ =
      d.componentMixedPosition externalTime σ B p :=
  d.componentMixedPositionEquiv_apply externalTime σ B p

/-- Total oriented crossing count between distinct connected components in ambient mixed order. -/
noncomputable def ExternalInsertionWickDiagram.mixedInterComponentCrossingCount
    {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) : ℕ :=
  (d.pairingInMixedOrder externalTime σ).interComponentCrossingCount
    (d.componentMixedPairEquiv externalTime σ)

/-- For two distinct components, mixed-order geometric crossing parity is exactly the parity of
ambient slot inversions between their mixed-position blocks. -/
theorem ExternalInsertionWickDiagram.mixedComponentCrossingCount_add_swap_mod_two_eq_blockInversionCount
    {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (B C : d.vertexGraph.componentPartition.parts) (hBC : B ≠ C) :
    ((d.pairingInMixedOrder externalTime σ).componentCrossingCount
        (d.componentMixedPairEquiv externalTime σ) B C +
      (d.pairingInMixedOrder externalTime σ).componentCrossingCount
        (d.componentMixedPairEquiv externalTime σ) C B) % 2 =
      (d.componentMixedPositionShuffle externalTime σ).blockInversionCount B C % 2 := by
  rw [← (d.pairingInMixedOrder externalTime σ).componentGeometricCrossingCount_eq_oriented_add
    (d.componentMixedPairEquiv externalTime σ) B C,
    (d.componentMixedPositionShuffle externalTime σ).blockInversionCount_of_ne hBC]
  simp only [ExternalInsertionWickDiagram.componentMixedPositionShuffle_slotEquiv_apply]
  exact
    Pairing.componentGeometricCrossingCount_mod_two_eq_endpointInversionCount
      (d.pairingInMixedOrder externalTime σ)
        (d.componentMixedPairEquiv externalTime σ)
        (fun D =>
          ((d.componentWickDiagram D).pairingInMixedOrder
            (d.componentExternalTime externalTime D)
            (d.componentInteractionTime σ D)).pairEndpointEquiv)
        (fun D p => d.componentMixedPosition externalTime σ D p)
        (fun D p k => by
          fin_cases k <;>
            simp [Pairing.pairEndpointEquiv_apply, Pairing.pairEndpoint, pairEndpointAt,
              d.componentMixedPairEquiv_apply externalTime σ])
        B C hBC

/-- The residual mixed-order inter-component crossing parity is the total inversion parity of the
canonical mixed component-position shuffle. -/
theorem ExternalInsertionWickDiagram.mixedInterComponentCrossingCount_mod_two_eq_orderedBlockInversionCount
    {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (blockOrder :
      d.vertexGraph.componentPartition.parts ≃
        Fin (Fintype.card d.vertexGraph.componentPartition.parts)) :
    d.mixedInterComponentCrossingCount externalTime σ % 2 =
      (d.componentMixedPositionShuffle externalTime σ).orderedBlockInversionCount blockOrder % 2 := by
  classical
  let pairing := d.pairingInMixedOrder externalTime σ
  let pairEquiv := d.componentMixedPairEquiv externalTime σ
  let cross := fun B C : d.vertexGraph.componentPartition.parts =>
    pairing.componentCrossingCount pairEquiv B C
  let inv := fun B C : d.vertexGraph.componentPartition.parts =>
    (d.componentMixedPositionShuffle externalTime σ).blockInversionCount B C
  let selected := fun B C : d.vertexGraph.componentPartition.parts =>
    if blockOrder B < blockOrder C then inv B C else 0
  have hsum :=
    finset_sum_offDiag_modEq_of_pair_add_modEq
      2 (Finset.univ : Finset d.vertexGraph.componentPartition.parts) cross selected
      (fun B _ C _ hBC => by
        by_cases hlt : blockOrder B < blockOrder C
        · have hnlt : ¬ blockOrder C < blockOrder B := asymm hlt
          simpa [Nat.ModEq, selected, hlt, hnlt, inv, cross, pairing, pairEquiv] using
            d.mixedComponentCrossingCount_add_swap_mod_two_eq_blockInversionCount
              externalTime σ B C hBC
        · have hneOrder : blockOrder B ≠ blockOrder C := by
            intro h
            exact hBC (blockOrder.injective h)
          have hrev : blockOrder C < blockOrder B := by
            rcases lt_trichotomy (blockOrder B) (blockOrder C) with h | h | h
            · exact absurd h hlt
            · exact absurd h hneOrder
            · exact h
          simpa [Nat.ModEq, selected, hlt, hrev, inv, cross, pairing, pairEquiv, add_comm] using
            d.mixedComponentCrossingCount_add_swap_mod_two_eq_blockInversionCount
              externalTime σ C B hBC.symm)
  simpa [Nat.ModEq, ExternalInsertionWickDiagram.mixedInterComponentCrossingCount,
    Pairing.interComponentCrossingCount, FamilySlotShuffleTo.orderedBlockInversionCount,
    cross, inv, selected, pairing, pairEquiv] using hsum

/-- The ambient mixed-order crossing count is the sum of the component-local mixed crossing counts
plus the residual crossings between distinct components. -/
theorem ExternalInsertionWickDiagram.pairingInMixedOrder_crossingCount_eq_sum_components_add_inter
    {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    (d.pairingInMixedOrder externalTime σ).crossingCount =
      (∑ B : d.vertexGraph.componentPartition.parts,
        ((d.componentWickDiagram B).pairingInMixedOrder
          (d.componentExternalTime externalTime B)
          (d.componentInteractionTime σ B)).crossingCount) +
        d.mixedInterComponentCrossingCount externalTime σ := by
  rw [Pairing.crossingCount_eq_sum_componentCrossingCount_diag_add_inter
    (d.pairingInMixedOrder externalTime σ)
    (d.componentMixedPairEquiv externalTime σ)]
  apply congrArg (fun k : ℕ => k + d.mixedInterComponentCrossingCount externalTime σ)
  apply Finset.sum_congr rfl
  intro B _
  exact Pairing.componentCrossingCount_self_eq
    (d.pairingInMixedOrder externalTime σ)
    ((d.componentWickDiagram B).pairingInMixedOrder
      (d.componentExternalTime externalTime B)
      (d.componentInteractionTime σ B))
    (d.componentMixedPairEquiv externalTime σ) B
    (Equiv.refl _)
    (d.componentMixedPosition externalTime σ B)
    (d.componentMixedPosition_strictMono externalTime σ B)
    (fun pr => by
      simpa using d.componentMixedPairEquiv_apply externalTime σ B pr)

/-- Mixed-order exchange-statistics weight factors into the residual inter-component mixed crossing
weight and the product of component-local mixed pairing weights. -/
theorem ExternalInsertionWickDiagram.pairingInMixedOrder_weight_eq_inter_mul_prod_components
    {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
    (s : Statistics)
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    (d.pairingInMixedOrder externalTime σ).weight s =
      (s.zetaInt : ℂ) ^ d.mixedInterComponentCrossingCount externalTime σ *
        ∏ B : d.vertexGraph.componentPartition.parts,
          ((d.componentWickDiagram B).pairingInMixedOrder
            (d.componentExternalTime externalTime B)
            (d.componentInteractionTime σ B)).weight s := by
  classical
  simp only [Pairing.weight]
  rw [d.pairingInMixedOrder_crossingCount_eq_sum_components_add_inter
    externalTime σ, pow_add, ← Finset.prod_pow_eq_pow_sum]
  exact mul_comm _ _

end Fermionic
end SecondQuantization
