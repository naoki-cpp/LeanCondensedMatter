import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ReassembleRestrictComponent
import LeanCondensedMatter.SecondQuantization.Fermionic.WickDiagram.ReassembleComponentPartitionEq

set_option linter.style.header false

/-!
# Fermionic restriction of a reassembled quartic diagram

This module preserves the fermionic API while delegating the label-generic proof to Common.
-/

namespace SecondQuantization

variable {Mode : Type*} {N : ℕ}

/-- Restricting a reassembled diagram to one partition block recovers that block's diagram. -/
theorem QuarticWickDiagram.restrictComponent_reassemble {S : Finset (Fin N)}
    (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticWickDiagram Mode N (B : Finset (Fin N)))
    (B : π.parts)
    (hB' : (B : Finset (Fin N)) ∈ (QuarticWickDiagram.reassemble π F).componentPartition.parts) :
    (QuarticWickDiagram.reassemble π F).restrictComponent hB' = (F B).1 :=
  Common.QuarticDiagram.restrictComponent_reassemble π F B hB'

end SecondQuantization
