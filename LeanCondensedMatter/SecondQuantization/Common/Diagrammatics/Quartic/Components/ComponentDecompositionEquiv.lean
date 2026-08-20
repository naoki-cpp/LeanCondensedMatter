import LeanCondensedMatter.Combinatorics.Cumulant.ConnectedDecomposition
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.ReassembleLaws

set_option linter.style.header false

/-!
# Labelled quartic-diagram component decomposition

Packages the component partition and connected component restrictions of a labelled quartic diagram
as an equivalence with a dependent family of connected diagrams, one on each partition block. The
inverse is `QuarticDiagram.reassemble`. The same decomposition is exposed directly through the
generic cumulant `ConnectedDecomposition` interface used by connected-diagram sums.
-/

namespace SecondQuantization
namespace Common

variable {Label : Type*} {N : ℕ}

/-- A labelled quartic diagram decomposed into its component partition and connected pieces. -/
noncomputable def QuarticDiagram.componentDecompose {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) :
    Σ π : Finpartition S,
      ∀ B : π.parts, ConnectedQuarticDiagram Label N (B : Finset (Fin N)) :=
  ⟨d.componentPartition, fun B => d.restrictComponentConnected B.2⟩

/-- Restricting a reassembled diagram as a connected diagram recovers the original block. -/
theorem QuarticDiagram.restrictComponentConnected_reassemble {S : Finset (Fin N)}
    (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticDiagram Label N (B : Finset (Fin N)))
    (B : π.parts)
    (hB' : (B : Finset (Fin N)) ∈ (QuarticDiagram.reassemble π F).componentPartition.parts) :
    (QuarticDiagram.reassemble π F).restrictComponentConnected hB' = F B := by
  apply Subtype.ext
  exact QuarticDiagram.restrictComponent_reassemble π F B hB'

private theorem QuarticDiagram.componentFamily_heq_of_partition_eq {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticDiagram Label N (B : Finset (Fin N)))
    (hπ : d.componentPartition = π)
    (hF : ∀ (B : Finset (Fin N)) (hBπ : B ∈ π.parts)
      (hBd : B ∈ d.componentPartition.parts),
      d.restrictComponentConnected hBd = F ⟨B, hBπ⟩) :
    HEq (fun B : d.componentPartition.parts => d.restrictComponentConnected B.2) F := by
  subst π
  apply heq_of_eq
  funext B
  simpa using hF B.1 B.2 B.2

private theorem QuarticDiagram.componentFamily_reassemble_heq {S : Finset (Fin N)}
    (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticDiagram Label N (B : Finset (Fin N))) :
    HEq
      (fun B : (QuarticDiagram.reassemble π F).componentPartition.parts =>
        (QuarticDiagram.reassemble π F).restrictComponentConnected B.2)
      F := by
  apply QuarticDiagram.componentFamily_heq_of_partition_eq
    (d := QuarticDiagram.reassemble π F) (π := π) (F := F)
    (QuarticDiagram.componentPartition_reassemble π F)
  intro B hBπ hBd
  exact QuarticDiagram.restrictComponentConnected_reassemble π F ⟨B, hBπ⟩ hBd

/-- Decomposing a reassembled family recovers the original dependent family. -/
theorem QuarticDiagram.componentDecompose_reassemble {S : Finset (Fin N)}
    (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticDiagram Label N (B : Finset (Fin N))) :
    QuarticDiagram.componentDecompose (QuarticDiagram.reassemble π F) = ⟨π, F⟩ := by
  apply Sigma.ext
  · exact QuarticDiagram.componentPartition_reassemble π F
  · exact QuarticDiagram.componentFamily_reassemble_heq π F

/-- Labelled quartic diagrams are equivalent to partitions carrying one connected diagram per block. -/
noncomputable def QuarticDiagram.componentDecompositionEquiv {S : Finset (Fin N)} :
    QuarticDiagram Label N S ≃
      Σ π : Finpartition S,
        ∀ B : π.parts, ConnectedQuarticDiagram Label N (B : Finset (Fin N)) where
  toFun := QuarticDiagram.componentDecompose
  invFun := fun x => QuarticDiagram.reassemble x.1 x.2
  left_inv := QuarticDiagram.reassemble_componentPartition
  right_inv := by
    rintro ⟨π, F⟩
    exact QuarticDiagram.componentDecompose_reassemble π F

/-- The statistics-independent connected-decomposition adapter for labelled quartic diagrams. -/
noncomputable def quarticDiagramConnectedDecomposition
    (Label : Type*) [Fintype Label] (N : ℕ) :
    Combinatorics.ConnectedDecomposition (Fin N) where
  Object S := QuarticDiagram Label N S
  ConnectedObject S := ConnectedQuarticDiagram Label N S
  fintypeObject _ := inferInstance
  fintypeConnectedObject _ := inferInstance
  decompose _ := QuarticDiagram.componentDecompositionEquiv

end Common
end SecondQuantization
