import LeanCondensedMatter.SecondQuantization.Common.QuarticDiagramComponentConnected
import LeanCondensedMatter.SecondQuantization.Fermionic.WickDiagram.ComponentRestriction

set_option linter.style.header false

/-!
# Fermionic connected component restrictions

This module specializes the label-generic connectedness proof for restricted quartic diagrams to
fermionic quartic vertex labels while preserving the existing public API.
-/

namespace SecondQuantization

variable {Mode : Type*} {N : ℕ}

noncomputable section

/-- A vertex of component part `B`, viewed as a vertex of the ambient set `S`. -/
noncomputable def QuarticWickDiagram.blockVertex {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts) (v : ↥B) : ↥S :=
  ((QuarticWickDiagram.subtypeMemBlockEquiv B (d.componentPart_subset hB)).symm v :
    {v : ↥S // (v : Fin N) ∈ B})

theorem QuarticWickDiagram.blockVertex_mem {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts) (v : ↥B) :
    (d.blockVertex hB v : Fin N) ∈ B := by
  simpa only [QuarticWickDiagram.blockVertex, Common.QuarticDiagram.blockVertex] using
    (Common.QuarticDiagram.blockVertex_mem d hB v)

theorem QuarticWickDiagram.vertexOfLeg_blockLegEquiv_eq_iff {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts)
    (leg : {leg : Fin (2 * (2 * S.card)) // d.legInBlock B leg}) (v : ↥B) :
    vertexOfLeg (d.blockLegEquiv hB leg) = v ↔
      vertexOfLeg (leg : Fin (2 * (2 * S.card))) = d.blockVertex hB v := by
  simpa only [QuarticWickDiagram.blockVertex, Common.QuarticDiagram.blockVertex] using
    (Common.QuarticDiagram.vertexOfLeg_blockLegEquiv_eq_iff d hB leg v)

theorem QuarticWickDiagram.restrictComponent_vertexGraph_adj_iff {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts) (u w : ↥B) :
    (d.restrictComponent hB).vertexGraph.Adj u w ↔
      d.vertexGraph.Adj (d.blockVertex hB u) (d.blockVertex hB w) := by
  simpa only [QuarticWickDiagram.blockVertex, Common.QuarticDiagram.blockVertex] using
    (Common.QuarticDiagram.restrictComponent_vertexGraph_adj_iff d hB u w)

theorem QuarticWickDiagram.blockVertex_subtypeMemBlockEquiv {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts) (v : ↥S) (hv : (v : Fin N) ∈ B) :
    d.blockVertex hB
        (QuarticWickDiagram.subtypeMemBlockEquiv B (d.componentPart_subset hB) ⟨v, hv⟩) = v := by
  simpa only [QuarticWickDiagram.blockVertex, Common.QuarticDiagram.blockVertex] using
    (Common.QuarticDiagram.blockVertex_subtypeMemBlockEquiv d hB v hv)

theorem QuarticWickDiagram.subtypeMemBlockEquiv_blockVertex {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts) (v : ↥B) :
    QuarticWickDiagram.subtypeMemBlockEquiv B (d.componentPart_subset hB)
        ⟨d.blockVertex hB v, d.blockVertex_mem hB v⟩ = v := by
  simpa only [QuarticWickDiagram.blockVertex, Common.QuarticDiagram.blockVertex] using
    (Common.QuarticDiagram.subtypeMemBlockEquiv_blockVertex d hB v)

/-- Restricting a fermionic diagram to a component part produces a connected diagram. -/
theorem QuarticWickDiagram.restrictComponent_isConnected {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts) :
    (d.restrictComponent hB).IsConnected :=
  Common.QuarticDiagram.restrictComponent_isConnected d hB

/-- `restrictComponent`, packaged as a connected fermionic quartic diagram. -/
noncomputable def QuarticWickDiagram.restrictComponentConnected {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts) : ConnectedQuarticWickDiagram Mode N B :=
  ⟨d.restrictComponent hB, d.restrictComponent_isConnected hB⟩

end

end SecondQuantization
