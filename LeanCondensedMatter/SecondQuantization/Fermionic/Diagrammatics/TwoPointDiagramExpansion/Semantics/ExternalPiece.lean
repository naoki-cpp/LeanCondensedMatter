import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Semantics.Reindexing
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.External.ExternalPiece

set_option linter.style.header false

/-!
# Fixed-external specialization of the standalone external piece

The statistics-independent standalone external diagram and all of its leg/mixed-position transport
are owned by `SecondQuantization.Common`. This file keeps only the fermionic fixed-external subtype
lift used by the physical contraction layer.
-/

namespace SecondQuantization
namespace Fermionic

open Common

variable {Mode : Type*} {n : ℕ} {i j : Mode}

/-- The Common standalone external piece, lifted to the fixed-external fermionic subtype. -/
noncomputable def FixedExternalTwoPointWickDiagram.externalPiece
    (d : FixedExternalTwoPointWickDiagram Mode n i j) :
    FixedExternalTwoPointWickDiagram Mode d.1.externalInteractionPart.card i j :=
  ⟨d.1.externalPiece, by
    rw [Common.TwoPointDiagram.externalPiece_externalLabel]
    exact d.2⟩

end Fermionic
end SecondQuantization
