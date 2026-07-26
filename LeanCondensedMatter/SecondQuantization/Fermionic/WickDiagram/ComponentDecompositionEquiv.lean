import LeanCondensedMatter.SecondQuantization.Common.QuarticDiagramComponentDecompositionEquiv
import LeanCondensedMatter.SecondQuantization.Fermionic.WickDiagram.ReassembleDecompose
import LeanCondensedMatter.SecondQuantization.Fermionic.WickDiagram.ReassembleRestrictComponent

set_option linter.style.header false

/-!
# Fermionic quartic-diagram component-decomposition equivalence

This module preserves the fermionic API while delegating the label-generic equivalence to Common.
-/

namespace SecondQuantization

variable {Mode : Type*} {N : ℕ}

/-- A quartic Wick diagram decomposed into its component partition and connected pieces. -/
noncomputable abbrev QuarticWickDiagram.componentDecompose {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) :
    Σ π : Finpartition S,
      ∀ B : π.parts, ConnectedQuarticWickDiagram Mode N (B : Finset (Fin N)) :=
  Common.QuarticDiagram.componentDecompose d

/-- Restricting a reassembled diagram as a connected diagram recovers the original block. -/
theorem QuarticWickDiagram.restrictComponentConnected_reassemble {S : Finset (Fin N)}
    (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticWickDiagram Mode N (B : Finset (Fin N)))
    (B : π.parts)
    (hB' : (B : Finset (Fin N)) ∈ (QuarticWickDiagram.reassemble π F).componentPartition.parts) :
    (QuarticWickDiagram.reassemble π F).restrictComponentConnected hB' = F B :=
  Common.QuarticDiagram.restrictComponentConnected_reassemble π F B hB'

/-- Decomposing a reassembled family recovers the original dependent family. -/
theorem QuarticWickDiagram.componentDecompose_reassemble {S : Finset (Fin N)}
    (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticWickDiagram Mode N (B : Finset (Fin N))) :
    QuarticWickDiagram.componentDecompose (QuarticWickDiagram.reassemble π F) = ⟨π, F⟩ :=
  Common.QuarticDiagram.componentDecompose_reassemble π F

/-- Quartic Wick diagrams are equivalent to partitions carrying one connected diagram per block. -/
noncomputable abbrev QuarticWickDiagram.componentDecompositionEquiv {S : Finset (Fin N)} :
    QuarticWickDiagram Mode N S ≃
      Σ π : Finpartition S,
        ∀ B : π.parts, ConnectedQuarticWickDiagram Mode N (B : Finset (Fin N)) :=
  Common.QuarticDiagram.componentDecompositionEquiv

end SecondQuantization
