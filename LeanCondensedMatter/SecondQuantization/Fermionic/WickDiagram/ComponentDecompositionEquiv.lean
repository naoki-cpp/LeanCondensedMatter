import LeanCondensedMatter.SecondQuantization.Fermionic.WickDiagram.ReassembleRestrictComponent

set_option linter.style.header false

/-!
# Quartic Wick diagram component-decomposition equivalence

Packages the component partition and connected component restrictions of a quartic Wick diagram as
an equivalence with a dependent family of connected diagrams, one on each partition block. The
inverse is `QuarticWickDiagram.reassemble`.

The two inverse laws are the previously proved `reassemble_componentPartition` and the converse
combination of `componentPartition_reassemble` with `restrictComponent_reassemble`.
-/

namespace SecondQuantization

variable {Mode : Type*} {N : ℕ}

/-- **A quartic Wick diagram decomposed into its component partition and connected pieces.** -/
noncomputable def QuarticWickDiagram.componentDecompose {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) :
    Σ π : Finpartition S,
      ∀ B : π.parts, ConnectedQuarticWickDiagram Mode N (B : Finset (Fin N)) :=
  ⟨d.componentPartition, fun B => d.restrictComponentConnected B.2⟩

/-- **Restricting a reassembled diagram as a connected diagram recovers the original block.** -/
theorem QuarticWickDiagram.restrictComponentConnected_reassemble {S : Finset (Fin N)}
    (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticWickDiagram Mode N (B : Finset (Fin N)))
    (B : π.parts)
    (hB' : (B : Finset (Fin N)) ∈ (QuarticWickDiagram.reassemble π F).componentPartition.parts) :
    (QuarticWickDiagram.reassemble π F).restrictComponentConnected hB' = F B := by
  apply Subtype.ext
  exact QuarticWickDiagram.restrictComponent_reassemble π F B hB'

private theorem QuarticWickDiagram.componentFamily_heq_of_partition_eq {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticWickDiagram Mode N (B : Finset (Fin N)))
    (hπ : d.componentPartition = π)
    (hF : ∀ (B : Finset (Fin N)) (hBπ : B ∈ π.parts)
      (hBd : B ∈ d.componentPartition.parts),
      d.restrictComponentConnected hBd = F ⟨B, hBπ⟩) :
    HEq (fun B : d.componentPartition.parts => d.restrictComponentConnected B.2) F := by
  subst π
  apply Eq.heq
  funext B
  simpa using hF B.1 B.2 B.2

/-- **The connected component family of a reassembled diagram is heterogeneously equal to `F`.** -/
private theorem QuarticWickDiagram.componentFamily_reassemble_heq {S : Finset (Fin N)}
    (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticWickDiagram Mode N (B : Finset (Fin N))) :
    HEq
      (fun B : (QuarticWickDiagram.reassemble π F).componentPartition.parts =>
        (QuarticWickDiagram.reassemble π F).restrictComponentConnected B.2)
      F := by
  apply QuarticWickDiagram.componentFamily_heq_of_partition_eq
    (d := QuarticWickDiagram.reassemble π F) (π := π) (F := F)
    (QuarticWickDiagram.componentPartition_reassemble π F)
  intro B hBπ hBd
  exact QuarticWickDiagram.restrictComponentConnected_reassemble π F ⟨B, hBπ⟩ hBd

/-- **Decomposing a reassembled family recovers the original dependent family.** -/
theorem QuarticWickDiagram.componentDecompose_reassemble {S : Finset (Fin N)}
    (π : Finpartition S)
    (F : ∀ B : π.parts, ConnectedQuarticWickDiagram Mode N (B : Finset (Fin N))) :
    QuarticWickDiagram.componentDecompose (QuarticWickDiagram.reassemble π F) = ⟨π, F⟩ := by
  apply Sigma.ext
  · exact QuarticWickDiagram.componentPartition_reassemble π F
  · exact QuarticWickDiagram.componentFamily_reassemble_heq π F

end SecondQuantization
