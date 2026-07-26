import LeanCondensedMatter.SecondQuantization.Common.QuarticDiagramComponentDecompositionEquiv
import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.QuarticDiagram

set_option linter.style.header false

/-!
# Bosonic quartic-diagram component-decomposition equivalence

The label-generic Common inverse laws specialize directly to bosonic quartic diagrams. This module
exposes the resulting decomposition and reassembly API under Bosonic names without introducing any
fermionic dependency.
-/

namespace SecondQuantization
namespace Bosonic

variable {Mode : Type*} {N : ℕ}

/-- The component partition of a reassembled bosonic family is the original partition. -/
theorem QuarticDiagram.componentPartition_reassemble {S : Finset (Fin N)}
    (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticDiagram Mode N (B : Finset (Fin N))) :
    (QuarticDiagram.reassemble π F).componentPartition = π :=
  Common.QuarticDiagram.componentPartition_reassemble π F

/-- Restricting a reassembled bosonic diagram recovers the original block diagram. -/
theorem QuarticDiagram.restrictComponent_reassemble {S : Finset (Fin N)}
    (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticDiagram Mode N (B : Finset (Fin N)))
    (B : π.parts)
    (hB' : (B : Finset (Fin N)) ∈ (QuarticDiagram.reassemble π F).componentPartition.parts) :
    (QuarticDiagram.reassemble π F).restrictComponent hB' = (F B).1 :=
  Common.QuarticDiagram.restrictComponent_reassemble π F B hB'

/-- Reassembling a bosonic diagram's connected component restrictions recovers the diagram. -/
theorem QuarticDiagram.reassemble_componentPartition {S : Finset (Fin N)}
    (d : QuarticDiagram Mode N S) :
    QuarticDiagram.reassemble d.componentPartition
      (fun B => d.restrictComponentConnected B.2) = d :=
  Common.QuarticDiagram.reassemble_componentPartition d

/-- A bosonic quartic diagram decomposed into its component partition and connected pieces. -/
noncomputable abbrev QuarticDiagram.componentDecompose {S : Finset (Fin N)}
    (d : QuarticDiagram Mode N S) :
    Σ π : Finpartition S,
      ∀ B : π.parts, ConnectedQuarticDiagram Mode N (B : Finset (Fin N)) :=
  Common.QuarticDiagram.componentDecompose d

/-- Restricting a reassembled diagram as a connected diagram recovers the original block. -/
theorem QuarticDiagram.restrictComponentConnected_reassemble {S : Finset (Fin N)}
    (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticDiagram Mode N (B : Finset (Fin N)))
    (B : π.parts)
    (hB' : (B : Finset (Fin N)) ∈ (QuarticDiagram.reassemble π F).componentPartition.parts) :
    (QuarticDiagram.reassemble π F).restrictComponentConnected hB' = F B :=
  Common.QuarticDiagram.restrictComponentConnected_reassemble π F B hB'

/-- Decomposing a reassembled bosonic family recovers the original dependent family. -/
theorem QuarticDiagram.componentDecompose_reassemble {S : Finset (Fin N)}
    (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticDiagram Mode N (B : Finset (Fin N))) :
    QuarticDiagram.componentDecompose (QuarticDiagram.reassemble π F) = ⟨π, F⟩ :=
  Common.QuarticDiagram.componentDecompose_reassemble π F

/-- Bosonic quartic diagrams are equivalent to partitions carrying one connected diagram per block. -/
noncomputable abbrev QuarticDiagram.componentDecompositionEquiv {S : Finset (Fin N)} :
    QuarticDiagram Mode N S ≃
      Σ π : Finpartition S,
        ∀ B : π.parts, ConnectedQuarticDiagram Mode N (B : Finset (Fin N)) :=
  Common.QuarticDiagram.componentDecompositionEquiv

end Bosonic
end SecondQuantization
