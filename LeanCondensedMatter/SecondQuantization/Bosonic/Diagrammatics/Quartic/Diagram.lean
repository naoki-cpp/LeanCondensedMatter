import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Components.Reassemble
import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.Quartic.Interaction

set_option linter.style.header false

/-!
# Bosonic quartic diagrams

This module supplies the two bosonic type aliases needed to specialize the label-generic
`Common.QuarticDiagram` API to the statistics-independent `Common.QuarticVertexLabel`.

Graph, connectedness, component restriction and reassembly, vertex-order transport, and ordered-data
results are used directly from `Common`; no Bosonic forwarding declarations are introduced here.
-/

namespace SecondQuantization
namespace Bosonic

variable {Mode : Type*} {N : ℕ}

/-- A bosonic quartic diagram on the interaction vertices in `S`. -/
abbrev QuarticDiagram (Mode : Type*) (N : ℕ) (S : Finset (Fin N)) :=
  Common.QuarticDiagram (Common.QuarticVertexLabel Mode) N S

/-- A connected bosonic quartic diagram. -/
abbrev ConnectedQuarticDiagram (Mode : Type*) (N : ℕ) (S : Finset (Fin N)) :=
  Common.ConnectedQuarticDiagram (Common.QuarticVertexLabel Mode) N S

end Bosonic
end SecondQuantization
