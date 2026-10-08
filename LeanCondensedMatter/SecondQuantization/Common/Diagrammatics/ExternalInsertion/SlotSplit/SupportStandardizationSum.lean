import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.SlotSplit.SupportStandardization
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.SlotSplit.ExternalSupportFiber

set_option linter.style.header false

/-!
# Standardized sums over external-support fibers

At total interaction order `m + k`, the left-support slot sets are equivalent to
`SlotShuffle m k`. For each shuffle, the external-support fiber is then equivalent
to a vacuum-free external diagram on `Fin m` and ordered quartic data on `Fin k`.

This is a finite reindexing for arbitrary diagram weights. No Dyson-amplitude
factorization or connectedness of distinct external components is assumed.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*}

open Classical in
/-- Reindex a fixed-cardinality external-support sum by shuffles and standardized,
shuffle-independent diagram data. -/
theorem ExternalInsertionDiagram.sum_leftSlotSet_standardizedSupportFiber
    [Fintype ExternalLabel] [Fintype InternalLabel]
    {E m k : ℕ} {R : Type*} [AddCommMonoid R]
    (F : ExternalInsertionDiagram ExternalLabel InternalLabel E (m + k)
      (Finset.univ : Finset (Fin (m + k))) → R) :
    (∑ T : LeftSlotSet m k,
      ∑ p : {ext : ExternalInsertionDiagram ExternalLabel InternalLabel E (m + k)
          T.1 // HasNoVacuumComponent ext.vertexGraph} ×
        QuarticDiagram InternalLabel (m + k)
          ((Finset.univ : Finset (Fin (m + k))) \ T.1),
        F ((ExternalInsertionDiagram.externalSupportFiberEquiv
            (Finset.subset_univ T.1)).symm p).1) =
      ∑ shuffle : SlotShuffle m k,
        ∑ q : {ext : ExternalInsertionDiagram ExternalLabel InternalLabel E m
              (Finset.univ : Finset (Fin m)) //
              HasNoVacuumComponent ext.vertexGraph} ×
            OrderedQuarticDiagramData InternalLabel k,
          F ((ExternalInsertionDiagram.externalSupportFiberEquiv
              (Finset.subset_univ shuffle.leftSlots)).symm
              ((ExternalInsertionDiagram.standardizedSupportFiberDataEquiv
                (E := E) shuffle).symm q)).1 := by
  classical
  rw [sum_leftSlotSet]
  change
    (∑ shuffle : SlotShuffle m k,
      ∑ p : {ext : ExternalInsertionDiagram ExternalLabel InternalLabel E (m + k)
          shuffle.leftSlots // HasNoVacuumComponent ext.vertexGraph} ×
        QuarticDiagram InternalLabel (m + k)
          ((Finset.univ : Finset (Fin (m + k))) \ shuffle.leftSlots),
        F ((ExternalInsertionDiagram.externalSupportFiberEquiv
            (Finset.subset_univ shuffle.leftSlots)).symm p).1) = _
  apply Finset.sum_congr rfl
  intro shuffle _
  exact (Equiv.sum_comp
    (ExternalInsertionDiagram.standardizedSupportFiberDataEquiv (E := E) shuffle).symm
    (fun p => F ((ExternalInsertionDiagram.externalSupportFiberEquiv
      (Finset.subset_univ shuffle.leftSlots)).symm p).1)).symm

end Common
end SecondQuantization
