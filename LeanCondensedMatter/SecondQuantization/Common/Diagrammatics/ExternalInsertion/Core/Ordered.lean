import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Core.Diagram
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.ExternalInsertionMixedOrder

set_option linter.style.header false

/-!
# Full-slot coordinates of external-insertion diagrams

The internal labels and pairing partner are expressed using consecutive interaction slots and
canonical external/interaction leg identities. These coordinates do not depend on particle
statistics or concrete label types.
-/

namespace SecondQuantization
namespace Common

variable {ExternalLabel InternalLabel : Type*}

/-- Slot-indexed interaction labels of an external-insertion diagram. -/
def ExternalInsertionDiagram.vertexLabelSequence {E n : ℕ}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E n
      (Finset.univ : Finset (Fin n))) :
    Fin n → InternalLabel :=
  fun v => d.vertexLabel ⟨v, Finset.mem_univ v⟩

/-- The diagram pairing as a map on canonical external/interaction leg identities. -/
noncomputable def ExternalInsertionDiagram.atomicLegPartner {E n : ℕ}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E n
      (Finset.univ : Finset (Fin n)))
    (leg : OrderedExternalInsertionLeg E n) : OrderedExternalInsertionLeg E n :=
  externalInsertionLegEquiv E (Finset.univ : Finset (Fin n))
    (d.pairing.partner
      ((externalInsertionLegEquiv E (Finset.univ : Finset (Fin n))).symm leg))

end Common
end SecondQuantization
