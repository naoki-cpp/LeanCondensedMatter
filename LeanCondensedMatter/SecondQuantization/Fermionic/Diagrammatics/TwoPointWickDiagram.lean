import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Core.Diagram
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.FieldLabel
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.QuarticInteraction

set_option linter.style.header false

/-!
# Fermionic two-point Wick diagrams

This module keeps the fermionic label specialization of the statistics-independent two-point diagram
data. Connectedness, component restrictions, and other reusable diagram structure remain owned by
`SecondQuantization.Common` and are imported directly by downstream consumers that need them.
-/

namespace SecondQuantization
namespace Fermionic

/-- A fermionic two-point diagram with one annihilation leg, one creation leg, and quartic
interaction vertices. -/
abbrev TwoPointWickDiagram (Mode : Type*) (N : ℕ) (S : Finset (Fin N)) :=
  Common.TwoPointDiagram (ExternalFieldLabel Mode) (QuarticVertexLabel Mode) N S

end Fermionic
end SecondQuantization
