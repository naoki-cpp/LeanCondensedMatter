import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.SlotSplitVacuumComponents
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.ComponentVertexProduct

set_option linter.style.header false

/-!
# Vertex products on the vacuum side of a two-point slot split

For an externally connected left piece, `slotSplitVacuumComponentEquiv` identifies the vacuum
components of the reassembled two-point diagram with the connected components of the quartic right
piece.  This module records the corresponding product identity for arbitrary vertex-local weights.
It is the statistics-independent prefactor bridge used by the linked-cluster amplitude proof.
-/

namespace SecondQuantization
namespace Common

variable {ExternalLabel InternalLabel : Type*} {N : ℕ} {S T : Finset (Fin N)}

/-- On one corresponding vacuum component, the ambient two-point vertex product agrees with the
vertex product on the quartic component restriction. -/
theorem TwoPointDiagram.prod_slotSplitVacuumComponentPart_eq_restrictComponent
    {M : Type*} [CommMonoid M]
    (h : T ⊆ S)
    (ext : TwoPointDiagram ExternalLabel InternalLabel N T)
    (vac : QuarticDiagram InternalLabel N (S \ T))
    (w : InternalLabel → M) (C : vac.componentPartition.parts) :
    (∏ v : ↥(TwoPointDiagram.interactionPart
        (((slotSplitVacuumComponentPart h ext vac C).1.1 :
          Finset (TwoPointVertex S)))),
      w ((TwoPointDiagram.ofSlotSplit h ext vac).vertexLabel
        ⟨v.1, TwoPointDiagram.interactionPart_subset
          ((slotSplitVacuumComponentPart h ext vac C).1.1 :
            Finset (TwoPointVertex S)) v.2⟩)) =
      ∏ v : ↥(C : Finset (Fin N)),
        w ((vac.restrictComponent C.2).vertexLabel v) := by
  classical
  let A : Finset (Fin N) := TwoPointDiagram.interactionPart
    (((slotSplitVacuumComponentPart h ext vac C).1.1 : Finset (TwoPointVertex S)))
  have hpart : A = (C : Finset (Fin N)) := by
    exact interactionPart_slotSplitVacuumComponentPart h ext vac C
  let e : ↥A ≃ ↥(C : Finset (Fin N)) :=
    { toFun := fun v : ↥A =>
        (⟨v.1, by
          rw [← hpart]
          exact v.2⟩ : ↥(C : Finset (Fin N)))
      invFun := fun v : ↥(C : Finset (Fin N)) =>
        (⟨v.1, by
          rw [hpart]
          exact v.2⟩ : ↥A)
      left_inv := fun v => Subtype.ext rfl
      right_inv := fun v => Subtype.ext rfl }
  change (∏ v : ↥A,
      w ((TwoPointDiagram.ofSlotSplit h ext vac).vertexLabel
        ⟨v.1, TwoPointDiagram.interactionPart_subset
          ((slotSplitVacuumComponentPart h ext vac C).1.1 :
            Finset (TwoPointVertex S)) v.2⟩)) = _
  calc
    (∏ v : ↥A,
        w ((TwoPointDiagram.ofSlotSplit h ext vac).vertexLabel
          ⟨v.1, TwoPointDiagram.interactionPart_subset
            ((slotSplitVacuumComponentPart h ext vac C).1.1 :
              Finset (TwoPointVertex S)) v.2⟩)) =
      ∏ v : ↥A, w ((vac.restrictComponent C.2).vertexLabel (e v)) := by
        apply Fintype.prod_congr
        intro v
        rw [TwoPointDiagram.ofSlotSplit_vertexLabel_of_not_mem]
        · unfold QuarticDiagram.restrictComponent
          congr 2
          apply Subtype.ext
          rfl
        · have hvComp : (v : Fin N) ∈ S \ T :=
            vac.componentPart_subset C.2 (e v).2
          exact (Finset.mem_sdiff.mp hvComp).2
    _ = ∏ v : ↥(C : Finset (Fin N)),
        w ((vac.restrictComponent C.2).vertexLabel v) :=
      Equiv.prod_comp e (fun v => w ((vac.restrictComponent C.2).vertexLabel v))

/-- The product of arbitrary vertex-local weights over all ambient vacuum components is exactly the
product over all vertices of the standalone quartic vacuum piece. -/
theorem TwoPointDiagram.prod_slotSplitVacuumComponents_eq_vacuumVertexProduct
    {M : Type*} [CommMonoid M]
    (h : T ⊆ S)
    (ext : TwoPointDiagram ExternalLabel InternalLabel N T)
    (vac : QuarticDiagram InternalLabel N (S \ T))
    (hext : ext.IsExternallyConnected) (w : InternalLabel → M) :
    (TwoPointDiagram.ofSlotSplit h ext vac).vacuumComponentParts.prod (fun B =>
      ∏ v : ↥(TwoPointDiagram.interactionPart
        (B : Finset (TwoPointVertex S))),
        w ((TwoPointDiagram.ofSlotSplit h ext vac).vertexLabel
          ⟨v.1, TwoPointDiagram.interactionPart_subset
            (B : Finset (TwoPointVertex S)) v.2⟩)) =
      ∏ v : ↥(S \ T), w (vac.vertexLabel v) := by
  classical
  calc
    (TwoPointDiagram.ofSlotSplit h ext vac).vacuumComponentParts.prod (fun B =>
        ∏ v : ↥(TwoPointDiagram.interactionPart
          (B : Finset (TwoPointVertex S))),
          w ((TwoPointDiagram.ofSlotSplit h ext vac).vertexLabel
            ⟨v.1, TwoPointDiagram.interactionPart_subset
              (B : Finset (TwoPointVertex S)) v.2⟩)) =
      ∏ B : ↥(TwoPointDiagram.ofSlotSplit h ext vac).vacuumComponentParts,
        ∏ v : ↥(TwoPointDiagram.interactionPart
          (B.1 : Finset (TwoPointVertex S))),
          w ((TwoPointDiagram.ofSlotSplit h ext vac).vertexLabel
            ⟨v.1, TwoPointDiagram.interactionPart_subset
              (B.1 : Finset (TwoPointVertex S)) v.2⟩) := by
        exact Finset.prod_subtype
          (TwoPointDiagram.ofSlotSplit h ext vac).vacuumComponentParts
          (fun _ => Iff.rfl) _
    _ = ∏ C : vac.componentPartition.parts,
        ∏ v : ↥(TwoPointDiagram.interactionPart
          (((slotSplitVacuumComponentEquiv h ext vac hext C).1.1 :
            Finset (TwoPointVertex S)))),
          w ((TwoPointDiagram.ofSlotSplit h ext vac).vertexLabel
            ⟨v.1, TwoPointDiagram.interactionPart_subset
              ((slotSplitVacuumComponentEquiv h ext vac hext C).1.1 :
                Finset (TwoPointVertex S)) v.2⟩) := by
      exact (Equiv.prod_comp (slotSplitVacuumComponentEquiv h ext vac hext)
        (fun B =>
          ∏ v : ↥(TwoPointDiagram.interactionPart
            (B.1 : Finset (TwoPointVertex S))),
            w ((TwoPointDiagram.ofSlotSplit h ext vac).vertexLabel
              ⟨v.1, TwoPointDiagram.interactionPart_subset
                (B.1 : Finset (TwoPointVertex S)) v.2⟩))).symm
    _ = ∏ C : vac.componentPartition.parts,
        ∏ v : ↥(C : Finset (Fin N)),
          w ((vac.restrictComponent C.2).vertexLabel v) := by
      apply Fintype.prod_congr
      intro C
      rw [slotSplitVacuumComponentEquiv_apply]
      exact TwoPointDiagram.prod_slotSplitVacuumComponentPart_eq_restrictComponent
        h ext vac w C
    _ = ∏ v : ↥(S \ T), w (vac.vertexLabel v) :=
      (vac.prod_vertexLabel_eq_prod_restrictComponent w).symm

/-- The product of the Dyson signs carried by the ambient vacuum components is the Dyson sign of the
whole quartic vacuum piece. -/
theorem TwoPointDiagram.prod_slotSplitVacuumComponentSigns_eq
    (h : T ⊆ S)
    (ext : TwoPointDiagram ExternalLabel InternalLabel N T)
    (vac : QuarticDiagram InternalLabel N (S \ T))
    (hext : ext.IsExternallyConnected) :
    (TwoPointDiagram.ofSlotSplit h ext vac).vacuumComponentParts.prod (fun B =>
      (-1 : ℂ) ^ (TwoPointDiagram.interactionPart
        (B : Finset (TwoPointVertex S))).card) =
      (-1 : ℂ) ^ (S \ T).card := by
  classical
  calc
    (TwoPointDiagram.ofSlotSplit h ext vac).vacuumComponentParts.prod (fun B =>
        (-1 : ℂ) ^ (TwoPointDiagram.interactionPart
          (B : Finset (TwoPointVertex S))).card) =
      ∏ B : ↥(TwoPointDiagram.ofSlotSplit h ext vac).vacuumComponentParts,
        (-1 : ℂ) ^ (TwoPointDiagram.interactionPart
          (B.1 : Finset (TwoPointVertex S))).card := by
        exact Finset.prod_subtype
          (TwoPointDiagram.ofSlotSplit h ext vac).vacuumComponentParts
          (fun _ => Iff.rfl) _
    _ = ∏ C : vac.componentPartition.parts,
        (-1 : ℂ) ^ (TwoPointDiagram.interactionPart
          (((slotSplitVacuumComponentEquiv h ext vac hext C).1.1 :
            Finset (TwoPointVertex S)))).card := by
      exact (Equiv.prod_comp (slotSplitVacuumComponentEquiv h ext vac hext)
        (fun B => (-1 : ℂ) ^ (TwoPointDiagram.interactionPart
          (B.1 : Finset (TwoPointVertex S))).card)).symm
    _ = ∏ C : vac.componentPartition.parts,
        (-1 : ℂ) ^ (C : Finset (Fin N)).card := by
      apply Fintype.prod_congr
      intro C
      rw [slotSplitVacuumComponentEquiv_apply,
        interactionPart_slotSplitVacuumComponentPart]
    _ = (-1 : ℂ) ^ (S \ T).card :=
      (vac.dysonSign_eq_prod_componentSigns).symm

end Common
end SecondQuantization
