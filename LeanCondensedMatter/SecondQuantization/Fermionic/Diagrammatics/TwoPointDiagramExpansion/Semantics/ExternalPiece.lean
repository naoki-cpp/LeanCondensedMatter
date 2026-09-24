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

/-- The Common standalone external piece with a chosen target slot count, lifted to the
fixed-external fermionic subtype. -/
noncomputable def FixedExternalTwoPointWickDiagram.externalPieceOfCardEq
    (d : FixedExternalTwoPointWickDiagram Mode n i j) {m : ℕ}
    (h : d.1.externalInteractionPart.card = m) :
    FixedExternalTwoPointWickDiagram Mode m i j :=
  ⟨d.1.externalPieceOfCardEq h, by
    rw [Common.TwoPointDiagram.externalPieceOfCardEq_externalLabel]
    exact d.2⟩

/-- The Common standalone external piece, lifted to the fixed-external fermionic subtype. -/
noncomputable def FixedExternalTwoPointWickDiagram.externalPiece
    (d : FixedExternalTwoPointWickDiagram Mode n i j) :
    FixedExternalTwoPointWickDiagram Mode d.1.externalInteractionPart.card i j :=
  ⟨d.1.externalPiece, by
    change (d.1.externalPieceOfCardEq rfl).externalLabel = d.1.externalLabel
    exact Common.TwoPointDiagram.externalPieceOfCardEq_externalLabel d.1 rfl
      |>.trans d.2⟩

end Fermionic
end SecondQuantization
