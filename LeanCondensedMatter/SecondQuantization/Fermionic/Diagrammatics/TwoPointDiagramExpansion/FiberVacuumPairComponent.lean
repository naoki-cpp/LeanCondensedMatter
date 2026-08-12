import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.FiberVacuumPairImage

set_option linter.style.header false

/-!
# Component index of a fixed-order vacuum pair

The fixed-order quartic vacuum pairing and the ambient mixed two-point pairing now have an exact
normalized-pair correspondence.  This module records the compatible component index: the quartic
component containing the first endpoint is sent to the ambient vacuum component produced by
`slotSplitVacuumComponentPart`.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics

variable {Mode : Type*} {n : ℕ} {i j : Mode}

/-- The connected component of the standalone quartic diagram containing a fixed-order normalized
pair. -/
noncomputable def QuarticWickDiagram.fixedOrderPairComponent
    {N : ℕ} {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (order : Common.QuarticVertexOrder S)
    (pr : (d.pairingInOrder order).NormalizedPair) : d.componentPartition.parts :=
  let q := Common.orderedLegToDiagramLeg S order pr.1.1
  ⟨d.componentBlock (Common.vertexOfLeg q),
    d.componentBlock_mem_componentPartition (Common.vertexOfLeg q)⟩

@[simp]
theorem QuarticWickDiagram.fixedOrderPairComponent_val
    {N : ℕ} {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (order : Common.QuarticVertexOrder S)
    (pr : (d.pairingInOrder order).NormalizedPair) :
    (d.fixedOrderPairComponent order pr : Finset (Fin N)) =
      d.componentBlock
        (Common.vertexOfLeg (Common.orderedLegToDiagramLeg S order pr.1.1)) :=
  rfl

/-- The component of an embedded vacuum pair is exactly the ambient component corresponding to its
standalone quartic component. -/
theorem fixedExternalOfSlotSplitVacuumNormalizedPairEmbedding_pairComponent
    (T : Finset (Fin n))
    (ext : FixedExternalTwoPointWickDiagramOn Mode n T i j)
    (vac : QuarticWickDiagram Mode n ((Finset.univ : Finset (Fin n)) \ T))
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hσ : StrictAnti (σ ∘ fixedExternalVacuumSlot T))
    (pr : (vac.pairingInOrder (fixedExternalVacuumOrder T)).NormalizedPair) :
    let d := fixedExternalOfSlotSplit T ext vac
    d.mixedPairComponent τ τ' σ
        (fixedExternalOfSlotSplitVacuumNormalizedPairEmbedding T ext vac τ τ' σ hσ pr) =
      (Common.slotSplitVacuumComponentPart (Finset.subset_univ T) ext.1 vac
        (vac.fixedOrderPairComponent (fixedExternalVacuumOrder T) pr)).1 := by
  let d := fixedExternalOfSlotSplit T ext vac
  let q := Common.orderedLegToDiagramLeg
    ((Finset.univ : Finset (Fin n)) \ T) (fixedExternalVacuumOrder T) pr.1.1
  let v : ↥((Finset.univ : Finset (Fin n)) \ T) := Common.vertexOfLeg q
  let C : vac.componentPartition.parts :=
    vac.fixedOrderPairComponent (fixedExternalVacuumOrder T) pr
  rw [fixedExternalOfSlotSplitVacuumNormalizedPairEmbedding_component
    T ext vac τ τ' σ hσ pr]
  let B : d.1.componentPartition.parts :=
    ⟨d.1.componentBlock (Common.slotSplitVacuumVertex v),
      d.1.componentBlock_mem_componentPartition (Common.slotSplitVacuumVertex v)⟩
  let D : d.1.componentPartition.parts :=
    (Common.slotSplitVacuumComponentPart (Finset.subset_univ T) ext.1 vac C).1
  change B = D
  let w : ↥(Finset.univ : Finset (Fin n)) := ⟨v.1, Finset.mem_univ _⟩
  apply d.1.interactionPart_component_unique w B D
  · apply (Common.TwoPointDiagram.mem_interactionPart_subtype
      (B : Finset (Common.TwoPointVertex (Finset.univ : Finset (Fin n)))) w).2
    exact d.1.self_mem_componentBlock (Common.slotSplitVacuumVertex v)
  · rw [show D = (Common.slotSplitVacuumComponentPart
        (Finset.subset_univ T) ext.1 vac C).1 by rfl,
      Common.interactionPart_slotSplitVacuumComponentPart]
    change (v.1 : Fin n) ∈ (C : Finset (Fin n))
    change (v.1 : Fin n) ∈ vac.componentBlock v
    exact vac.self_mem_componentBlock v

end Fermionic
end SecondQuantization
