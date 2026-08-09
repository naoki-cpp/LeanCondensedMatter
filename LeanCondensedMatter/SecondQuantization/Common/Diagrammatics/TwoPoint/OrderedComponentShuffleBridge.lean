import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.CanonicalComponentShuffle
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.OrderedComponentShuffleTransport

set_option linter.style.header false

/-!
# Canonical component shuffle under interaction ordering

The canonical component shuffle of an explicitly ordered two-point diagram, transported back to the
ambient diagram, is characterized through the ambient slots occupied by each component.  This avoids
exposing dependent local-index casts in downstream finite-order reindexing.
-/

namespace SecondQuantization
namespace Common

variable {ExternalLabel InternalLabel : Type*} {N : ℕ}

noncomputable section

/-- The explicit interaction slots belonging to the ordered copy of an ambient component are exactly
the global slots occupied by that component under the chosen interaction order. -/
theorem TwoPointDiagram.interactionPart_inInteractionOrderComponentPartEquiv_symm
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (order : QuarticVertexOrder S) (B : d.componentPartition.parts) :
    TwoPointDiagram.interactionPart
        (((d.inInteractionOrderComponentPartEquiv order).symm B :
          (d.inInteractionOrder order).componentPartition.parts) :
          Finset (TwoPointVertex (Finset.univ : Finset (Fin S.card)))) =
      d.componentInteractionGlobalSlots order B := by
  classical
  ext v
  let vExplicit : ↥(Finset.univ : Finset (Fin S.card)) :=
    ⟨v, Finset.mem_univ v⟩
  let vAmbient : ↥S := order v
  constructor
  · intro hv
    have hvFull : (Sum.inr vExplicit :
        TwoPointVertex (Finset.univ : Finset (Fin S.card))) ∈
        (((d.inInteractionOrderComponentPartEquiv order).symm B :
          (d.inInteractionOrder order).componentPartition.parts) :
          Finset (TwoPointVertex (Finset.univ : Finset (Fin S.card)))) :=
      (TwoPointDiagram.mem_interactionPart_subtype _ vExplicit).1 hv
    change (Sum.inr vExplicit :
        TwoPointVertex (Finset.univ : Finset (Fin S.card))) ∈
      B.1.image (twoPointInteractionOrderVertexEquiv order).symm at hvFull
    obtain ⟨x, hx, hxeq⟩ := Finset.mem_image.mp hvFull
    have hxEq : x = (Sum.inr vAmbient : TwoPointVertex S) := by
      apply (twoPointInteractionOrderVertexEquiv order).symm.injective
      rw [hxeq]
      simp [vAmbient, vExplicit, twoPointInteractionOrderVertexEquiv,
        finEquivUnivSubtype]
    have hvB : (Sum.inr vAmbient : TwoPointVertex S) ∈ B.1 := by
      simpa [hxEq] using hx
    have hvInt : (vAmbient : Fin N) ∈
        TwoPointDiagram.interactionPart (B : Finset (TwoPointVertex S)) :=
      (TwoPointDiagram.mem_interactionPart_subtype
        (B : Finset (TwoPointVertex S)) vAmbient).2 hvB
    let w : ↥(TwoPointDiagram.interactionPart
        (B : Finset (TwoPointVertex S))) := ⟨vAmbient.1, hvInt⟩
    have hwAmbient : d.interactionVertexComponentEquiv.symm ⟨B, w⟩ = vAmbient := by
      apply Subtype.ext
      simpa [w, vAmbient] using
        d.interactionVertexComponentEquiv_symm_val (⟨B, w⟩)
    apply Finset.mem_image.mpr
    refine ⟨w, Finset.mem_univ w, ?_⟩
    simp [TwoPointDiagram.componentInteractionGlobalSlot, hwAmbient, vAmbient]
  · intro hv
    change v ∈ Finset.univ.image (d.componentInteractionGlobalSlot order B) at hv
    obtain ⟨w, _, hw⟩ := Finset.mem_image.mp hv
    let wAmbient : ↥S :=
      ⟨w.1, TwoPointDiagram.interactionPart_subset
        (B : Finset (TwoPointVertex S)) w.2⟩
    have hcomponent : d.interactionVertexComponentEquiv.symm ⟨B, w⟩ = wAmbient := by
      apply Subtype.ext
      simpa [wAmbient] using
        d.interactionVertexComponentEquiv_symm_val (⟨B, w⟩)
    have hwB : (Sum.inr wAmbient : TwoPointVertex S) ∈ B.1 :=
      (TwoPointDiagram.mem_interactionPart_subtype
        (B : Finset (TwoPointVertex S)) wAmbient).1 w.2
    have hwSlot : order.symm wAmbient = v := by
      simpa [TwoPointDiagram.componentInteractionGlobalSlot, hcomponent] using hw
    have hwAmbient : wAmbient = vAmbient := by
      apply order.symm.injective
      simpa [vAmbient] using hwSlot
    have hvB : (Sum.inr vAmbient : TwoPointVertex S) ∈ B.1 := by
      simpa [hwAmbient] using hwB
    apply (TwoPointDiagram.mem_interactionPart_subtype _ vExplicit).2
    change (Sum.inr vExplicit :
        TwoPointVertex (Finset.univ : Finset (Fin S.card))) ∈
      B.1.image (twoPointInteractionOrderVertexEquiv order).symm
    apply Finset.mem_image.mpr
    refine ⟨Sum.inr vAmbient, hvB, ?_⟩
    simp [vAmbient, vExplicit, twoPointInteractionOrderVertexEquiv,
      finEquivUnivSubtype]

/-- Every slot occupied by the transported canonical shuffle belongs to the ambient component's
set of global interaction slots. -/
theorem TwoPointDiagram.inInteractionOrderComponentShuffleEquiv_canonical_mem_globalSlots
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (order : QuarticVertexOrder S) (B : d.componentPartition.parts)
    (i : Fin (d.interactionComponentSize B)) :
    (d.inInteractionOrderComponentShuffleEquiv order
        (d.inInteractionOrder order).canonicalComponentInteractionShuffle).slotEquiv ⟨B, i⟩ ∈
      d.componentInteractionGlobalSlots order B := by
  classical
  simp [TwoPointDiagram.inInteractionOrderComponentShuffleEquiv,
    TwoPointDiagram.componentInteractionFamilyShuffleEquiv,
    Combinatorics.FamilySlotShuffle.reindexEquiv,
    Combinatorics.FamilySlotShuffleTo.castTotalEquiv,
    TwoPointDiagram.canonicalComponentInteractionShuffle,
    TwoPointDiagram.interactionPart_inInteractionOrderComponentPartEquiv_symm,
    TwoPointDiagram.componentInteractionGlobalSlots]

end

end Common
end SecondQuantization
