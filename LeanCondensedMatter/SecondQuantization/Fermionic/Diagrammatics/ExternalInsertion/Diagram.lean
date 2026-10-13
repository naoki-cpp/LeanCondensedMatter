import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Core.Ordered
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Pairing.MixedOrder
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.Quartic.LocalLeg

set_option linter.style.header false

/-!
# Fermionic external-insertion diagrams

The concrete diagram uses external field labels and quartic vertex labels. Ordered coordinates,
component data, and mixed-order pairing transport are statistics-independent Common constructions.
-/

namespace SecondQuantization
namespace Fermionic

/-- Fermionic external-insertion diagrams with ordered interaction slots. -/
abbrev ExternalInsertionWickDiagram (Mode : Type*) (E n : ℕ) : Type _ :=
  Common.ExternalInsertionDiagram (ExternalFieldLabel Mode) (QuarticVertexLabel Mode)
    E n (Finset.univ : Finset (Fin n))

end Fermionic
end SecondQuantization
