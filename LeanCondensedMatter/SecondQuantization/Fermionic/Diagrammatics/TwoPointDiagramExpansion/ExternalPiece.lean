import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Reindexing
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ExternalPiece

set_option linter.style.header false

/-!
# Fixed-external specialization of the standalone external piece

The statistics-independent standalone external diagram and all of its leg/mixed-position transport
are owned by `SecondQuantization.Common`.  This file keeps only the fermionic fixed-external subtype
lift and the quartic-label sequence statement used by the physical contraction layer.
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

/-- The standardized external piece reads its quartic label from the corresponding ambient slot. -/
@[simp]
theorem FixedExternalTwoPointWickDiagram.externalPiece_vertexLabelSequence
    (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (v : Fin d.1.externalInteractionPart.card) :
    d.externalPiece.vertexLabelSequence v =
      d.1.vertexLabel
        ⟨d.1.externalInteractionPart.orderEmbOfFin rfl v, Finset.mem_univ _⟩ := by
  exact d.1.externalPiece_vertexLabel v

end Fermionic
end SecondQuantization
