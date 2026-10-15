import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.SlotSplit.ExternalSupportSplit

set_option linter.style.header false

/-!
# Canonical external-support diagram decomposition

Every external-insertion diagram splits canonically into an external-bearing diagram containing
all externally supported interaction vertices and an ordinary quartic diagram containing the
remaining vacuum interaction vertices. This module extracts the actual diagrams from the
support-based split and records their exact reconstruction.

The extracted external-bearing diagram may have several disconnected externally supported
components. Proving that it has no *vacuum* components is the next step, before reindexing the
diagram sum by vacuum-free fibers.
-/

namespace SecondQuantization
namespace Common

variable {ExternalLabel InternalLabel : Type*} {E N : ℕ}

/-- The external-bearing diagram obtained by retaining all connected components meeting the
external sector. Multiple externally supported connected components are retained. -/
noncomputable def ExternalInsertionDiagram.externalSupportDiagram
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S) :
    ExternalInsertionDiagram ExternalLabel InternalLabel E N
      d.externallySupportedInteractionPart :=
  d.slotSplitExternal d.externallySupportedInteractionPart_subset
    d.pairing_isSplit_externallySupportedInteractionPart

/-- The ordinary quartic diagram formed by the vacuum components of an external-insertion
diagram. -/
noncomputable def ExternalInsertionDiagram.vacuumComplementDiagram
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S) :
    QuarticDiagram InternalLabel N (S \ d.externallySupportedInteractionPart) :=
  d.slotSplitVacuum d.externallySupportedInteractionPart_subset
    d.pairing_isSplit_externallySupportedInteractionPart

/-- The canonical external-bearing and vacuum diagrams reconstruct the original diagram. -/
theorem ExternalInsertionDiagram.externalSupport_reconstruction
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S) :
    ExternalInsertionDiagram.ofSlotSplit
        d.externallySupportedInteractionPart_subset
        d.externalSupportDiagram d.vacuumComplementDiagram = d :=
  d.ofSlotSplit_slotSplit d.externallySupportedInteractionPart_subset
    d.pairing_isSplit_externallySupportedInteractionPart

end Common
end SecondQuantization
