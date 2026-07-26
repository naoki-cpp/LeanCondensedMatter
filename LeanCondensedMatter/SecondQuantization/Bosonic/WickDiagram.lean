import LeanCondensedMatter.SecondQuantization.Common.QuarticVertexLabel
import LeanCondensedMatter.SecondQuantization.Common.QuarticDiagramConnected

set_option linter.style.header false

/-!
# Bosonic quartic Wick diagrams

Bosonic quartic diagrams specialize the statistics-independent labelled diagram structures to
`Common.QuarticVertexLabel Mode`. Their stored data and connectedness are purely combinatorial;
bosonic contraction weights and amplitudes belong in later layers.
-/

namespace SecondQuantization

variable {Mode : Type*} {N : ℕ}

/-- A labelled quartic diagram whose vertices describe bosonic interaction vertices. -/
abbrev BosonicQuarticDiagram (Mode : Type*) (N : ℕ) (S : Finset (Fin N)) :=
  Common.QuarticDiagram (Common.QuarticVertexLabel Mode) N S

/-- The subtype of connected bosonic quartic diagrams on vertex set `S`. -/
abbrev ConnectedBosonicQuarticDiagram (Mode : Type*) (N : ℕ) (S : Finset (Fin N)) : Type _ :=
  Common.ConnectedQuarticDiagram (Common.QuarticVertexLabel Mode) N S

end SecondQuantization
