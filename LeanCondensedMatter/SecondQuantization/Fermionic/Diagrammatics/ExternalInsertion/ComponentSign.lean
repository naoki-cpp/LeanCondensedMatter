import LeanCondensedMatter.Combinatorics.FamilySlotShuffleInversions
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
  change (-1 : ℂ) ^ _ = (-1 : ℂ) ^ _
  exact pow_eq_of_mod_two_eq (by norm_num) hmod

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
  have hzero (B : d.vertexGraph.componentPartition.parts) (hBA : B ≠ A) :
      d.externalPairCount B = 0 := by
    have hEmpty :
        (B : Finset (Common.ExternalInsertionVertex E S)).toLeft = ∅ := by
      by_contra hNonempty
      obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hNonempty
      have hsupported : B ∈ Common.externallySupportedComponentParts d.vertexGraph :=
        (Common.mem_externallySupportedComponentParts d.vertexGraph B).2
          ⟨e, Finset.mem_toLeft.mp he⟩
      rw [hsingle] at hsupported
      exact hBA (Finset.mem_singleton.mp hsupported)
    simp [Common.ExternalInsertionDiagram.externalPairCount, hEmpty]
  have hpair (B C : d.vertexGraph.componentPartition.parts) (hBC : B ≠ C) :
      d.componentExternalShuffle.blockInversionCount B C = 0 := by
    rw [d.componentExternalShuffle.blockInversionCount_of_ne hBC]
    by_cases hBA : B = A
    · subst B
      have hCzero : d.externalPairCount C = 0 := hzero C hBC.symm
      simp [hCzero]
    · have hBzero : d.externalPairCount B = 0 := hzero B hBA
      simp [hBzero]
  have hcount :
      d.componentExternalShuffle.orderedBlockInversionCount blockOrder = 0 := by
    unfold Combinatorics.FamilySlotShuffleTo.orderedBlockInversionCount
    apply Finset.sum_eq_zero
    intro BC hBC
    have hne : BC.1 ≠ BC.2 := (Finset.mem_offDiag.mp hBC).2.2
    simp [hpair BC.1 BC.2 hne]
  unfold componentExternalOrderSign
  rw [hcount]
  simp

end Fermionic
end SecondQuantization
