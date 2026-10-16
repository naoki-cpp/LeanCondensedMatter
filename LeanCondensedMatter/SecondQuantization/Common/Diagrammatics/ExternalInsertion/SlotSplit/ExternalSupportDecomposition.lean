import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.SlotSplit.ExternalSupportSplit

set_option linter.style.header false

/-!
# External-bearing / vacuum diagram decomposition

Every external-insertion diagram splits canonically into an external-bearing diagram containing
all externally supported interaction vertices and an ordinary quartic diagram containing the
remaining vacuum interaction vertices. This module extracts the actual diagrams from the
support-based split and records their exact reconstruction.

The external-bearing diagram may contain multiple mutually disconnected components, each
meeting at least one external insertion. Its absence of purely vacuum components is proved
in `ExternalSupportConnectivity`; this does not imply full external connectedness.
-/

namespace SecondQuantization
namespace Common

variable {ExternalLabel InternalLabel : Type*} {E N : ℕ}

/-- The external-bearing diagram obtained by retaining all connected components meeting the
external sector. Multiple externally supported connected components are retained. -/
noncomputable def ExternalInsertionDiagram.externalBearingDiagram
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S) :
    ExternalInsertionDiagram ExternalLabel InternalLabel E N
      d.externallySupportedInteractionPart :=
  d.slotSplitExternal d.externallySupportedInteractionPart_subset
    d.pairing_isSplit_externallySupportedInteractionPart

/-- The ordinary quartic diagram formed by the vacuum components of an external-insertion
diagram. -/
noncomputable def ExternalInsertionDiagram.vacuumDiagram
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S) :
    QuarticDiagram InternalLabel N (S \ d.externallySupportedInteractionPart) :=
  d.slotSplitVacuum d.externallySupportedInteractionPart_subset
    d.pairing_isSplit_externallySupportedInteractionPart

/-- The canonical external-bearing and vacuum diagrams reconstruct the original diagram. -/
theorem ExternalInsertionDiagram.externalBearing_vacuum_reconstruction
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S) :
    ExternalInsertionDiagram.ofSlotSplit
        d.externallySupportedInteractionPart_subset
        d.externalBearingDiagram d.vacuumDiagram = d :=
  d.ofSlotSplit_slotSplit d.externallySupportedInteractionPart_subset
    d.pairing_isSplit_externallySupportedInteractionPart

end Common
end SecondQuantization
