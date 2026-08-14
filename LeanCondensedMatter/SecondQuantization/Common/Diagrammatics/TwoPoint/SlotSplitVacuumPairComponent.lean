import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.SlotSplitVacuumPairImage

set_option linter.style.header false

/-!
# Component index of a slot-split vacuum pair

A normalized pair of the fixed-order quartic vacuum pairing has a canonical quartic connected
component. Under the Common vacuum-pair embedding, that component is exactly the corresponding
ambient vacuum component of the reassembled two-point diagram.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*}

/-- The connected component of a quartic diagram containing the first endpoint of a normalized pair
in a chosen fixed vertex order. -/
noncomputable def QuarticDiagram.fixedOrderPairComponent
    {N : ℕ} {S : Finset (Fin N)} (d : QuarticDiagram InternalLabel N S)
    (order : QuarticVertexOrder S)
    (pr : (d.pairingInOrder order).NormalizedPair) : d.componentPartition.parts :=
  let q := orderedLegToDiagramLeg S order pr.1.1
  ⟨d.componentBlock (vertexOfLeg q),
    d.componentBlock_mem_componentPartition (vertexOfLeg q)⟩

@[simp]
theorem QuarticDiagram.fixedOrderPairComponent_val
    {N : ℕ} {S : Finset (Fin N)} (d : QuarticDiagram InternalLabel N S)
    (order : QuarticVertexOrder S)
    (pr : (d.pairingInOrder order).NormalizedPair) :
    (d.fixedOrderPairComponent order pr : Finset (Fin N)) =
      d.componentBlock (vertexOfLeg (orderedLegToDiagramLeg S order pr.1.1)) :=
  rfl

/-- The component of an embedded vacuum pair is exactly the ambient component corresponding to its
standalone quartic component. -/
theorem TwoPointDiagram.slotSplitVacuumNormalizedPairEmbedding_pairComponent
    {n : ℕ} (T : Finset (Fin n))
    (ext : TwoPointDiagram ExternalLabel InternalLabel n T)
    (vac : QuarticDiagram InternalLabel n ((Finset.univ : Finset (Fin n)) \ T))
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hσ : StrictAnti (σ ∘ slotSplitVacuumSlot T))
    (pr : (vac.pairingInOrder (slotSplitVacuumOrder T)).NormalizedPair) :
    let d := TwoPointDiagram.ofSlotSplit (Finset.subset_univ T) ext vac
    d.mixedPairComponent τ τ' σ
        (TwoPointDiagram.slotSplitVacuumNormalizedPairEmbedding T ext vac τ τ' σ hσ pr) =
      (slotSplitVacuumComponentPart (Finset.subset_univ T) ext vac
        (vac.fixedOrderPairComponent (slotSplitVacuumOrder T) pr)).1 := by
  let d := TwoPointDiagram.ofSlotSplit (Finset.subset_univ T) ext vac
  let q := orderedLegToDiagramLeg
    ((Finset.univ : Finset (Fin n)) \ T) (slotSplitVacuumOrder T) pr.1.1
  let v : ↥((Finset.univ : Finset (Fin n)) \ T) := vertexOfLeg q
  let C : vac.componentPartition.parts :=
    vac.fixedOrderPairComponent (slotSplitVacuumOrder T) pr
  change d.mixedPairComponent τ τ' σ
      (TwoPointDiagram.slotSplitVacuumNormalizedPairEmbedding
        T ext vac τ τ' σ hσ pr) = _
  rw [TwoPointDiagram.ofSlotSplitVacuumNormalizedPairEmbedding_component
    T ext vac τ τ' σ hσ pr]
  let B : d.componentPartition.parts :=
    ⟨d.componentBlock (slotSplitVacuumVertex v),
      d.componentBlock_mem_componentPartition (slotSplitVacuumVertex v)⟩
  let D : d.componentPartition.parts :=
    (slotSplitVacuumComponentPart (Finset.subset_univ T) ext vac C).1
  change B = D
  let w : ↥(Finset.univ : Finset (Fin n)) := ⟨v.1, Finset.mem_univ _⟩
  apply d.interactionPart_component_unique w B D
  · apply (TwoPointDiagram.mem_interactionPart_subtype
      (B : Finset (TwoPointVertex (Finset.univ : Finset (Fin n)))) w).2
    exact d.self_mem_componentBlock (slotSplitVacuumVertex v)
  · rw [show D = (slotSplitVacuumComponentPart
        (Finset.subset_univ T) ext vac C).1 by rfl,
      interactionPart_slotSplitVacuumComponentPart]
    change (v.1 : Fin n) ∈ (C : Finset (Fin n))
    change (v.1 : Fin n) ∈ vac.componentBlock v
    exact vac.self_mem_componentBlock v

end Common
end SecondQuantization
