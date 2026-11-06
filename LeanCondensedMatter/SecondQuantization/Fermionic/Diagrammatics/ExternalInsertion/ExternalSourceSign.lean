import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.ComponentSign
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.Diagram
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Components.ExternalPartition
import Mathlib.Data.Fintype.EquivFin

set_option linter.style.header false

/-!
# Fermionic external-source partition signs

The source convention fixes a canonical block order for the external-slot
shuffle. We compare it to the fermionic regrouping sign of actual Wick
diagram components, including the vacuum-free multi-component case.
The corresponding source sign is independent of physical Dyson coefficients.
-/

namespace SecondQuantization
namespace Fermionic

open Common
open scoped BigOperators

variable {Mode : Type*} {E : ℕ}

/-- A fixed convention for a partition's fermionic source sign. For partitions
with even blocks the choice of block order does not affect the result. Odd
blocks produce zero terms in the physical connected-diagram product. -/
noncomputable def externalPartitionSourceSign
    {S : Finset (Fin (2 * E))} (π : Finpartition S) : ℂ :=
  externalPartitionOrderSign π (Fintype.equivFin π.parts)

/-- Grouping an external set into a single source block has trivial
fermionic shuffle sign. This is the diagonal normalization needed for the
triangular source moment-to-cumulant transform. -/
theorem externalPartitionSourceSign_top
    (S : Finset (Fin (2 * E))) :
    externalPartitionSourceSign (⊤ : Finpartition S) = 1 := by
  classical
  haveI : Subsingleton (↥(⊤ : Finpartition S).parts) := by
    constructor
    intro B C
    apply Subtype.ext
    have hB : (B : Finset (Fin (2 * E))) = S :=
      Finset.mem_singleton.mp (Finpartition.parts_top_subset S B.2)
    have hC : (C : Finset (Fin (2 * E))) = S :=
      Finset.mem_singleton.mp (Finpartition.parts_top_subset S C.2)
    exact hB.trans hC.symm
  have hzero :
      (externalPartitionShuffle (⊤ : Finpartition S)).orderedBlockInversionCount
          (Fintype.equivFin (⊤ : Finpartition S).parts) = 0 := by
    unfold Combinatorics.FamilySlotShuffleTo.orderedBlockInversionCount
    apply Finset.sum_eq_zero
    intro BC hBC
    have hne := (Finset.mem_offDiag.mp hBC).2.2
    exact (hne (Subsingleton.elim BC.1 BC.2)).elim
  unfold externalPartitionSourceSign externalPartitionOrderSign
  rw [hzero]
  simp

/-- On a diagram whose external insertions are mutually connected,
the source-partition sign and the actual graph-component regrouping sign
agree: both are one. Pure-vacuum components may be present.

This is the top-partition case of the still-needed general signed
diagram/partition correspondence. -/
theorem externalPartitionSourceSign_eq_componentExternalOrderSign_of_connected
    {n : ℕ} (d : ExternalInsertionWickDiagram Mode E n)
    (anchor : Fin (2 * E))
    (hconnected : AllExternalVerticesConnected d.vertexGraph)
    (blockOrder : d.vertexGraph.componentPartition.parts ≃
      Fin (Fintype.card d.vertexGraph.componentPartition.parts)) :
    externalPartitionSourceSign (externalComponentPartition d.vertexGraph) =
      componentExternalOrderSign d blockOrder := by
  rw [(d.allExternalVerticesConnected_iff_externalComponentPartition_eq_top anchor).mp
    hconnected, externalPartitionSourceSign_top,
    componentExternalOrderSign_eq_one_of_allExternalVerticesConnected
      d anchor hconnected blockOrder]

/-- For every vacuum-free physical Wick diagram, its source external-partition
shuffle sign equals the sign obtained from the actual full-graph connected
components, with any chosen component order.

The proof uses the *sets of occupied ambient external slots*, rather than
casting between separately indexed local `Fin` types. The occupied sets agree
by the exact connected-component/external-block equivalence, and the order
independence uses even external component sizes. -/
theorem externalPartitionSourceSign_eq_componentExternalOrderSign_of_vacuumFree
    {n : ℕ} (d : ExternalInsertionWickDiagram Mode E n)
    (hVac : HasNoVacuumComponent d.vertexGraph)
    (blockOrder : d.vertexGraph.componentPartition.parts ≃
      Fin (Fintype.card d.vertexGraph.componentPartition.parts)) :
    externalPartitionSourceSign (externalComponentPartition d.vertexGraph) =
      componentExternalOrderSign d blockOrder := by
  classical
  let π := externalComponentPartition d.vertexGraph
  let e := d.vacuumFreeComponentsEquivExternalBlocks hVac
  let sourceOrder : π.parts ≃ Fin (Fintype.card π.parts) := Fintype.equivFin π.parts
  let hcard : Fintype.card d.vertexGraph.componentPartition.parts =
      Fintype.card π.parts := Fintype.card_congr e
  let compOrder : d.vertexGraph.componentPartition.parts ≃
      Fin (Fintype.card d.vertexGraph.componentPartition.parts) :=
    (e.trans sourceOrder).trans (Fin.castOrderIso hcard.symm).toEquiv
  have hset (B : d.vertexGraph.componentPartition.parts) :
      d.componentExternalShuffle.blockSlotSet B =
        (externalPartitionShuffleFull π).blockSlotSet (e B) := by
    rw [d.componentExternalShuffle_blockSlotSet,
      externalPartitionShuffleFull_blockSlotSet]
    exact (d.vacuumFreeComponentsEquivExternalBlocks_apply hVac B).symm
  have horder (B C : d.vertexGraph.componentPartition.parts) :
      compOrder B < compOrder C ↔
        sourceOrder (e B) < sourceOrder (e C) := by
    change (Fin.castOrderIso hcard.symm) (sourceOrder (e B)) <
        (Fin.castOrderIso hcard.symm) (sourceOrder (e C)) ↔ _
    constructor
    · intro h
      simpa using (Fin.castOrderIso hcard).strictMono h
    · intro h; exact (Fin.castOrderIso hcard.symm).strictMono h
  have hcount :
      d.componentExternalShuffle.orderedBlockInversionCount compOrder =
        (externalPartitionShuffleFull π).orderedBlockInversionCount sourceOrder :=
    d.componentExternalShuffle.orderedBlockInversionCount_eq_of_blockSlotSet
      (externalPartitionShuffleFull π) e hset compOrder sourceOrder horder
  calc
    externalPartitionSourceSign π =
        externalPartitionOrderSign π sourceOrder := rfl
    _ = (Common.Statistics.fermion.zetaInt : ℂ) ^
          (externalPartitionShuffleFull π).orderedBlockInversionCount sourceOrder := by
      unfold externalPartitionOrderSign
      rw [externalPartitionShuffleFull_orderedBlockInversionCount]
    _ = componentExternalOrderSign d compOrder := by
      unfold componentExternalOrderSign
      exact congrArg (fun n : ℕ => (Common.Statistics.fermion.zetaInt : ℂ) ^ n)
        hcount.symm
    _ = componentExternalOrderSign d blockOrder :=
      componentExternalOrderSign_eq_of_blockOrder d compOrder blockOrder


end Fermionic
end SecondQuantization
