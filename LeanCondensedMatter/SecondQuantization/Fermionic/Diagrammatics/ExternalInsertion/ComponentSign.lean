import LeanCondensedMatter.Combinatorics.FamilySlotShuffleInversions
import LeanCondensedMatter.SecondQuantization.Common.Algebra.Statistics
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Components.ComponentRestriction
import Mathlib.Analysis.Complex.Basic

set_option linter.style.header false

/-!
# Fermionic external-component shuffle sign

The canonical external-insertion component shuffle groups external legs by connected component,
preserving their increasing order within each block. Its ordered block-inversion count determines
the fermionic exchange sign that remains in component amplitude factorization.

The component order is explicit semantic input; time ordering is handled downstream.
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
