import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.SlotSplit.SlotSplitVacuumComponents
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Components.ComponentRestriction
import LeanCondensedMatter.Combinatorics.Common.FintypeProduct

set_option linter.style.header false

/-!
# Vertex products on the vacuum side of a two-point slot split

For an externally connected two-point piece, `slotSplitVacuumComponentEquiv` identifies the vacuum
components of the reconstructed diagram with the connected components of the quartic piece.

Reindexing along this equivalence factors arbitrary commutative products of vertex-local weights
over the vacuum components, including the corresponding interaction-vertex prefactors.
-/

namespace SecondQuantization
namespace Common

variable {ExternalLabel InternalLabel : Type*} {N : ℕ} {S T : Finset (Fin N)}

/-- On one corresponding vacuum component, the ambient two-point vertex product agrees with the
vertex product on the quartic component restriction. -/
private theorem TwoPointDiagram.prod_slotSplitVacuumComponentPart_eq_restrictComponent
    {M : Type*} [CommMonoid M]
    (h : T ⊆ S)
    (ext : TwoPointDiagram ExternalLabel InternalLabel N T)
    (vac : QuarticDiagram InternalLabel N (S \ T))
    (w : InternalLabel → M) (C : vac.vertexGraph.componentPartitionOn.parts) :
    (∏ v : ↥(interactionSector
        (((slotSplitVacuumComponentPart h ext vac C).1.1 :
          Finset (TwoPointVertex S)))),
      w ((TwoPointDiagram.ofSlotSplit h ext vac).vertexLabel
        ⟨v.1, interactionSector_subset
          ((slotSplitVacuumComponentPart h ext vac C).1.1 :
            Finset (TwoPointVertex S)) v.2⟩)) =
      ∏ v : ↥(C : Finset (Fin N)),
        w ((vac.restrictComponent C.2).vertexLabel v) := by
  classical
  let A : Finset (Fin N) := interactionSector
    (((slotSplitVacuumComponentPart h ext vac C).1.1 : Finset (TwoPointVertex S)))
  have hpart : A = (C : Finset (Fin N)) := by
    exact interactionSector_slotSplitVacuumComponentPart h ext vac C
  let e : ↥A ≃ ↥(C : Finset (Fin N)) :=
    Equiv.subtypeEquivRight fun v => by rw [hpart]
  change (∏ v : ↥A,
      w ((TwoPointDiagram.ofSlotSplit h ext vac).vertexLabel
        ⟨v.1, interactionSector_subset
          ((slotSplitVacuumComponentPart h ext vac C).1.1 :
            Finset (TwoPointVertex S)) v.2⟩)) = _
  calc
    (∏ v : ↥A,
        w ((TwoPointDiagram.ofSlotSplit h ext vac).vertexLabel
          ⟨v.1, interactionSector_subset
            ((slotSplitVacuumComponentPart h ext vac C).1.1 :
              Finset (TwoPointVertex S)) v.2⟩)) =
      ∏ v : ↥A, w ((vac.restrictComponent C.2).vertexLabel (e v)) := by
        apply Fintype.prod_congr
        intro v
        rw [TwoPointDiagram.ofSlotSplit_vertexLabel_of_not_mem]
        · unfold QuarticDiagram.restrictComponent
          congr 2
        · have hvComp : (v : Fin N) ∈ S \ T :=
            vac.vertexGraph.componentPartitionOn.le C.2 (e v).2
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
    (vacuumComponentParts (TwoPointDiagram.ofSlotSplit h ext vac).vertexGraph).prod (fun B =>
      ∏ v : ↥(interactionSector
        (B : Finset (TwoPointVertex S))),
        w ((TwoPointDiagram.ofSlotSplit h ext vac).vertexLabel
          ⟨v.1, interactionSector_subset
            (B : Finset (TwoPointVertex S)) v.2⟩)) =
      ∏ v : ↥(S \ T), w (vac.vertexLabel v) := by
  classical
  let d := TwoPointDiagram.ofSlotSplit h ext vac
  let e := slotSplitVacuumComponentEquiv h ext vac hext
  let F : d.vertexGraph.componentPartition.parts → M := fun B =>
    ∏ v : ↥(interactionSector (B.1 : Finset (TwoPointVertex S))),
      w (d.vertexLabel
        ⟨v.1, interactionSector_subset (B.1 : Finset (TwoPointVertex S)) v.2⟩)
  let G : vac.vertexGraph.componentPartitionOn.parts → M := fun C =>
    ∏ v : ↥(C : Finset (Fin N)), w ((vac.restrictComponent C.2).vertexLabel v)
  change (vacuumComponentParts d.vertexGraph).prod F =
    ∏ v : ↥(S \ T), w (vac.vertexLabel v)
  calc
    (vacuumComponentParts d.vertexGraph).prod F =
        ∏ B : ↥(vacuumComponentParts d.vertexGraph), F B.1 := by
      exact Finset.prod_subtype (vacuumComponentParts d.vertexGraph) (fun _ => Iff.rfl) F
    _ = ∏ C : vac.vertexGraph.componentPartitionOn.parts, F (e C).1 :=
      (Equiv.prod_comp e (fun B => F B.1)).symm
    _ = ∏ C : vac.vertexGraph.componentPartitionOn.parts, G C := by
      apply Fintype.prod_congr
      intro C
      simpa only [e, F, G, slotSplitVacuumComponentEquiv_apply] using
        (TwoPointDiagram.prod_slotSplitVacuumComponentPart_eq_restrictComponent
          h ext vac w C)
    _ = ∏ v : ↥(S \ T), w (vac.vertexLabel v) := by
      simpa only [G, QuarticDiagram.restrictComponent_vertexLabel_equivSigmaParts] using
        (Fintype.prod_equiv_sigma vac.vertexGraph.componentPartitionOn.equivSigmaParts
          (fun v => w (vac.vertexLabel v))).symm

end Common
end SecondQuantization
