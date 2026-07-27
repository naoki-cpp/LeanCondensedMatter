import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ReassembleDecompose
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.Reassemble

set_option linter.style.header false

/-!
# Fermionic reassembly from connected components

This module preserves the fermionic API while delegating the label-generic proof to Common.
-/

namespace SecondQuantization

variable {Mode : Type*} {N : ℕ}

/-- Reassembling a diagram's connected component restrictions recovers the diagram. -/
theorem QuarticWickDiagram.reassemble_componentPartition {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) :
    QuarticWickDiagram.reassemble d.componentPartition
      (fun B => d.restrictComponentConnected B.2) = d :=
  Common.QuarticDiagram.reassemble_componentPartition d

end SecondQuantization
