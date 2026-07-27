import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ReassembleComponentPartitionEq
import LeanCondensedMatter.SecondQuantization.Fermionic.WickDiagram.Reassemble

set_option linter.style.header false

/-!
# Fermionic component partition of a reassembled quartic diagram

This module preserves the fermionic API while delegating the label-generic proof to Common.
-/

namespace SecondQuantization

variable {Mode : Type*} {N : ℕ}

/-- A vertex of a block `B`, included back into the ambient vertex set. -/
noncomputable abbrev QuarticWickDiagram.reassembleVertex {S : Finset (Fin N)}
    (π : Finpartition S) (B : π.parts) (v : ↥(B : Finset (Fin N))) : ↥S :=
  Common.QuarticDiagram.reassembleVertex π B v

/-- The component partition of a reassembled family is the original partition. -/
theorem QuarticWickDiagram.componentPartition_reassemble {S : Finset (Fin N)}
    (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticWickDiagram Mode N (B : Finset (Fin N))) :
    (QuarticWickDiagram.reassemble π F).componentPartition = π :=
  Common.QuarticDiagram.componentPartition_reassemble π F

end SecondQuantization
