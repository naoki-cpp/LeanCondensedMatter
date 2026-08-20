import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Core.Connected
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.Quartic.Interaction

set_option linter.style.header false

/-!
# Fermionic quartic Wick diagrams

`QuarticWickDiagram Mode N S` specializes the statistics-independent
`Common.QuarticDiagram` to fermionic `QuarticVertexLabel Mode` labels. Creation and annihilation
semantics remain in the label and amplitude layers; the stored diagram data are only vertex labels
and a perfect pairing of the four legs per vertex.
-/

namespace SecondQuantization
namespace Fermionic

/-- A quartic diagram whose vertex labels describe fermionic interaction vertices. -/
abbrev QuarticWickDiagram (Mode : Type*) (N : ℕ) (S : Finset (Fin N)) :=
  Common.QuarticDiagram (QuarticVertexLabel Mode) N S

/-- A connected fermionic quartic diagram. -/
abbrev ConnectedQuarticWickDiagram (Mode : Type*) (N : ℕ) (S : Finset (Fin N)) :=
  Common.ConnectedQuarticDiagram (QuarticVertexLabel Mode) N S

end Fermionic
end SecondQuantization
