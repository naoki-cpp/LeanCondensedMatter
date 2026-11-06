import LeanCondensedMatter.Combinatorics.Shuffle.FamilySlotShuffleInversions
import LeanCondensedMatter.Combinatorics.Shuffle.FinpartitionOrderShuffle
import LeanCondensedMatter.Combinatorics.ExchangeSign
import LeanCondensedMatter.SecondQuantization.Common.Algebra.Statistics
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Components.ComponentRestriction
import Mathlib.Analysis.Complex.Basic

set_option linter.style.header false

/-!
# Fermionic external-component shuffle sign

The canonical external-insertion component shuffle groups external legs by connected component,
preserving their increasing order within each block. Its ordered block-inversion count determines
the fermionic exchange sign that remains in component amplitude factorization.

The component order is explicit in the componentwise factorization formula, but the
fermionic sign is invariant under that choice because each component has an
even external-leg count. Time ordering is handled downstream.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics

variable {ExternalLabel InternalLabel : Type*} {E N : ℕ}

/-- The increasing order of a finite family of external fermion slots. -/
private noncomputable def externalSubsetIncreasingOrder
    (S : Finset (Fin (2 * E))) : Fin S.card ≃ ↥S :=
  (S.orderIsoOfFin rfl).toEquiv

/-- The canonical shuffle of external slots within a finite subset, grouped by
blocks of a partition and kept in increasing order inside each block.

The source convention uses the increasing ambient slot order, restricted to
the subset at hand. It is independent of any interaction vertices. -/
noncomputable def externalPartitionShuffle
    {S : Finset (Fin (2 * E))} (π : Finpartition S) : π.PartShuffle := by
  let order := externalSubsetIncreasingOrder S
  let localOrders := π.partOrdersOfOrder order
  exact π.shuffleOfOrder order localOrders
    (π.partOrdersCompatible_partOrdersOfOrder order)

/-- Fermionic Koszul sign for grouping a subset of external insertions by
partition blocks. The order on the blocks is explicit, because the sign
of odd blocks need not be order independent. Physical nonvanishing blocks
have even cardinality. -/
noncomputable def externalPartitionOrderSign
    {S : Finset (Fin (2 * E))} (π : Finpartition S)
    (blockOrder : π.parts ≃ Fin (Fintype.card π.parts)) : ℂ :=
  (Common.Statistics.fermion.zetaInt : ℂ) ^
    (externalPartitionShuffle π).orderedBlockInversionCount blockOrder

/-- For even-sized external blocks, the source regrouping sign does not
depend on their arbitrary order. This applies to partitions of every
subset, not only the full family of external insertions. -/
theorem externalPartitionOrderSign_eq_of_blockOrder
    {S : Finset (Fin (2 * E))} (π : Finpartition S)
    (heven : ∀ B : π.parts, Even (B : Finset (Fin (2 * E))).card)
    (order₁ order₂ : π.parts ≃ Fin (Fintype.card π.parts)) :
    externalPartitionOrderSign π order₁ = externalPartitionOrderSign π order₂ := by
  unfold externalPartitionOrderSign
  exact pow_eq_of_mod_two_eq
    (ζ := (Common.Statistics.fermion.zetaInt : ℂ))
    (by norm_num [Common.Statistics.zetaInt_fermion])
    ((externalPartitionShuffle π).orderedBlockInversionCount_modEq_of_even_sizes
      order₁ order₂ heven)

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



/-- The fermionic external-component regrouping sign is independent of the
chosen order of full graph components, including the vacuum components.

Every component carries an even number of external fermion legs, so reversing
two component blocks changes the inversion count by an even number. -/
theorem componentExternalOrderSign_eq_of_blockOrder
    {S : Finset (Fin N)}
    (d : Common.ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (order₁ order₂ :
      d.vertexGraph.componentPartition.parts ≃
        Fin (Fintype.card d.vertexGraph.componentPartition.parts)) :
    componentExternalOrderSign d order₁ = componentExternalOrderSign d order₂ := by
  have hmod :
      Nat.ModEq 2
        (d.componentExternalShuffle.orderedBlockInversionCount order₁)
        (d.componentExternalShuffle.orderedBlockInversionCount order₂) :=
    d.componentExternalShuffle.orderedBlockInversionCount_modEq_of_even_sizes
      order₁ order₂ (fun B => ⟨d.externalPairCount B, by omega⟩)
  unfold componentExternalOrderSign
  exact pow_eq_of_mod_two_eq
    (ζ := (Common.Statistics.fermion.zetaInt : ℂ))
    (by norm_num [Common.Statistics.zetaInt_fermion]) hmod

/-- The external-order fermionic sign only involves connected components
meeting the external sector. Pure-vacuum components may occur anywhere in
the explicit block order but contribute no inversions. -/
theorem componentExternalOrderSign_eq_supportedParts
    {S : Finset (Fin N)}
    (d : Common.ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (blockOrder :
      d.vertexGraph.componentPartition.parts ≃
        Fin (Fintype.card d.vertexGraph.componentPartition.parts)) :
    componentExternalOrderSign d blockOrder =
      (Common.Statistics.fermion.zetaInt : ℂ) ^
        (∑ BC ∈ (Common.externallySupportedComponentParts d.vertexGraph).offDiag,
          if blockOrder BC.1 < blockOrder BC.2 then
            d.componentExternalShuffle.blockInversionCount BC.1 BC.2 else 0) := by
  classical
  let supported := Common.externallySupportedComponentParts d.vertexGraph
  let allParts : Finset d.vertexGraph.componentPartition.parts := Finset.univ
  let weight : d.vertexGraph.componentPartition.parts ×
      d.vertexGraph.componentPartition.parts → ℕ := fun BC =>
    if blockOrder BC.1 < blockOrder BC.2 then
      d.componentExternalShuffle.blockInversionCount BC.1 BC.2 else 0
  have hsub : supported.offDiag ⊆ allParts.offDiag := by
    intro BC hBC
    exact Finset.mem_offDiag.mpr
      ⟨Finset.mem_univ _, Finset.mem_univ _, (Finset.mem_offDiag.mp hBC).2.2⟩
  have hzero (BC : d.vertexGraph.componentPartition.parts ×
      d.vertexGraph.componentPartition.parts)
      (hBC : BC ∈ allParts.offDiag) (hnot : BC ∉ supported.offDiag) :
      weight BC = 0 := by
    have hne : BC.1 ≠ BC.2 := (Finset.mem_offDiag.mp hBC).2.2
    by_cases hB : BC.1 ∈ supported
    · by_cases hC : BC.2 ∈ supported
      · exact (hnot (Finset.mem_offDiag.mpr ⟨hB, hC, hne⟩)).elim
      · have hVac : Common.ComponentIsVacuum
            (BC.2 : Finset (Common.ExternalInsertionVertex E S)) :=
          fun h => hC ((Common.mem_externallySupportedComponentParts
            d.vertexGraph BC.2).2 h)
        simp [weight,
          d.componentExternalShuffle_blockInversionCount_zero_of_right_vacuum
            BC.1 BC.2 hVac]
    · have hVac : Common.ComponentIsVacuum
          (BC.1 : Finset (Common.ExternalInsertionVertex E S)) :=
        fun h => hB ((Common.mem_externallySupportedComponentParts
          d.vertexGraph BC.1).2 h)
      simp [weight,
        d.componentExternalShuffle_blockInversionCount_zero_of_left_vacuum
          BC.1 BC.2 hVac]
  change (Common.Statistics.fermion.zetaInt : ℂ) ^
      (∑ BC ∈ allParts.offDiag, weight BC) =
    (Common.Statistics.fermion.zetaInt : ℂ) ^
      (∑ BC ∈ supported.offDiag, weight BC)
  exact congrArg (fun k : ℕ => (Common.Statistics.fermion.zetaInt : ℂ) ^ k)
    (Finset.sum_subset hsub hzero).symm

/-- A diagram with all external insertions in one connected component has no
external regrouping sign, even if additional pure-vacuum components remain.

The chosen component order is immaterial: all other components carry zero
external slots and therefore contribute no inter-block inversions. -/
theorem componentExternalOrderSign_eq_one_of_allExternalVerticesConnected
    {S : Finset (Fin N)}
    (d : Common.ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (anchor : Fin (2 * E))
    (hconnected : Common.AllExternalVerticesConnected d.vertexGraph)
    (blockOrder :
      d.vertexGraph.componentPartition.parts ≃
        Fin (Fintype.card d.vertexGraph.componentPartition.parts)) :
    componentExternalOrderSign d blockOrder = 1 := by
  classical
  let A : d.vertexGraph.componentPartition.parts :=
    ⟨d.vertexGraph.componentBlock (Sum.inl anchor),
      d.vertexGraph.componentBlock_mem_componentPartition (Sum.inl anchor)⟩
  have hsingle : Common.externallySupportedComponentParts d.vertexGraph = {A} :=
    (Common.allExternalVerticesConnected_iff_supportedComponentParts_eq_singleton
      d.vertexGraph anchor).mp hconnected
  rw [componentExternalOrderSign_eq_supportedParts d blockOrder, hsingle]
  simp

end Fermionic
end SecondQuantization
