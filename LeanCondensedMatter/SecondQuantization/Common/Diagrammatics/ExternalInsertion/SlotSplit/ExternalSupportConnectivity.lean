import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.SlotSplit.ExternalSupportDecomposition
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Core.Connected

set_option linter.style.header false

/-!
# Vacuum-freeness of the canonical external-support diagram

The slot splitting preserves and reflects reachability between vertices on its external-bearing
side. Hence restricting a diagram to all components meeting the external sector leaves no vacuum
components, without requiring distinct external vertices to be mutually connected.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*} {E N : ℕ}
  {S T : Finset (Fin N)}

/-- Embed external-bearing vertices into the ambient vertex type of a slot split. -/
private def supportSlotVertex (h : T ⊆ S) :
    ExternalInsertionVertex E T → ExternalInsertionVertex E S
  | Sum.inl e => Sum.inl e
  | Sum.inr v => Sum.inr ⟨v.1, h v.2⟩

/-- The external-bearing and vacuum vertex sectors partition the ambient vertices. -/
private noncomputable def supportSlotVertexEquiv (h : T ⊆ S) :
    (ExternalInsertionVertex E T ⊕ ↥(S \ T)) ≃ ExternalInsertionVertex E S :=
  (Equiv.sumAssoc (Fin (2 * E)) ↥T ↥(S \ T)).trans
    (Equiv.sumCongr (Equiv.refl (Fin (2 * E))) (subsetSumSdiffEquiv h))

private theorem supportSlotVertexEquiv_inl (h : T ⊆ S) (x : ExternalInsertionVertex E T) :
    supportSlotVertexEquiv h (Sum.inl x) = supportSlotVertex h x := by
  cases x with
  | inl e => rfl
  | inr v =>
      change (Sum.inr (subsetSumSdiffEquiv h (Sum.inl v)) : ExternalInsertionVertex E S) =
        supportSlotVertex h (Sum.inr v)
      rw [subsetSumSdiffEquiv_inl_apply]
      rfl

private theorem supportSlotVertexEquiv_inr (h : T ⊆ S) (v : ↥(S \ T)) :
    supportSlotVertexEquiv (E := E) h (Sum.inr v) =
      (Sum.inr ⟨v.1, (Finset.mem_sdiff.mp v.2).1⟩ : ExternalInsertionVertex E S) := by
  change (Sum.inr (subsetSumSdiffEquiv h (Sum.inr v)) : ExternalInsertionVertex E S) = _
  rw [subsetSumSdiffEquiv_inr_apply]

/-- Left legs retain the corresponding vertices under the splitting. -/
private theorem supportSlotVertex_of_left_leg (h : T ⊆ S)
    (i : Fin (2 * (2 * T.card + E))) :
    externalInsertionVertexOfLeg
        (externalInsertionSlotLegSplitting (E := E) h (Sum.inl i)) =
      supportSlotVertex h (externalInsertionVertexOfLeg i) := by
  obtain ⟨x, rfl⟩ := (externalInsertionLegEquiv E T).symm.surjective i
  cases x with
  | inl e =>
      rw [externalInsertionSlotLegSplitting_external]
      simp [externalInsertionVertexOfLeg, supportSlotVertex]
  | inr p =>
      obtain ⟨v, l⟩ := p
      rw [externalInsertionSlotLegSplitting_left_interaction]
      simp [externalInsertionVertexOfLeg, supportSlotVertex]

/-- Right legs retain the corresponding quartic vertices under the splitting. -/
private theorem supportSlotVertex_of_right_leg (h : T ⊆ S)
    (i : Fin (2 * (2 * (S \ T).card))) :
    externalInsertionVertexOfLeg
        (externalInsertionSlotLegSplitting (E := E) h (Sum.inr i)) =
      supportSlotVertexEquiv (E := E) h (Sum.inr (vertexOfLeg i)) := by
  rw [supportSlotVertexEquiv_inr]
  obtain ⟨p, rfl⟩ := (quarticLegEquiv (S \ T)).symm.surjective i
  obtain ⟨v, l⟩ := p
  rw [externalInsertionSlotLegSplitting_right_interaction]
  simp [externalInsertionVertexOfLeg, vertexOfLeg]

variable (h : T ⊆ S)
    (ext : ExternalInsertionDiagram ExternalLabel InternalLabel E N T)
    (vac : QuarticDiagram InternalLabel N (S \ T))

/-- A split external-insertion diagram has the disjoint sum of its external-bearing
and vacuum vertex graphs. -/
private noncomputable def supportSlotVertexGraphIso :
    (ext.vertexGraph ⊕g vac.vertexGraph) ≃g
      (ExternalInsertionDiagram.ofSlotSplit h ext vac).vertexGraph :=
  Pairing.vertexGraphOfSplitIso (externalInsertionSlotLegSplitting (E := E) h)
    ext.pairing vac.pairing
    (externalInsertionVertexOfLeg (E := E) (S := T)) (vertexOfLeg (S := S \ T))
    (supportSlotVertexEquiv h) (externalInsertionVertexOfLeg (E := E) (S := S))
    (by
      intro i
      rw [supportSlotVertex_of_left_leg, supportSlotVertexEquiv_inl])
    (by
      intro i
      exact supportSlotVertex_of_right_leg h i)

/-- Reachability in the external-bearing piece is reflected by the disjoint graph sum. -/
private theorem supportSlotVertex_reachable_iff (x y : ExternalInsertionVertex E T) :
    (ExternalInsertionDiagram.ofSlotSplit h ext vac).vertexGraph.Reachable
        (supportSlotVertex h x) (supportSlotVertex h y) ↔
      ext.vertexGraph.Reachable x y := by
  rw [← supportSlotVertexEquiv_inl h x, ← supportSlotVertexEquiv_inl h y]
  change (ExternalInsertionDiagram.ofSlotSplit h ext vac).vertexGraph.Reachable
      ((supportSlotVertexGraphIso h ext vac) (Sum.inl x))
      ((supportSlotVertexGraphIso h ext vac) (Sum.inl y)) ↔ _
  exact (SimpleGraph.Iso.reachable_iff
    (φ := supportSlotVertexGraphIso h ext vac)
    (u := Sum.inl x) (v := Sum.inl y)).trans
      (SimpleGraph.reachable_sum_inl_iff ext.vertexGraph vac.vertexGraph x y)

/-- The canonical external-bearing diagram contains no pure-vacuum connected components.
All components touching distinct external insertions are retained independently. -/
theorem ExternalInsertionDiagram.hasNoVacuumComponent_externalSupportDiagram
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S) :
    HasNoVacuumComponent d.externalSupportDiagram.vertexGraph := by
  classical
  intro v
  let T := d.externallySupportedInteractionPart
  let h : T ⊆ S := d.externallySupportedInteractionPart_subset
  let ext := d.externalSupportDiagram
  let vac := d.vacuumComplementDiagram
  let vS : ↥S := ⟨v.1, h v.2⟩
  obtain ⟨e, he⟩ := (d.mem_externallySupportedInteractionPart vS).1 v.2
  have hreach : d.vertexGraph.Reachable (Sum.inl e) (Sum.inr vS) :=
    (d.vertexGraph.mem_componentBlock (Sum.inr vS) (Sum.inl e)).1 he
  have hD : ExternalInsertionDiagram.ofSlotSplit h ext vac = d :=
    d.externalSupport_reconstruction
  have hreach' :
      (ExternalInsertionDiagram.ofSlotSplit h ext vac).vertexGraph.Reachable
        (supportSlotVertex h (Sum.inl e))
        (supportSlotVertex h (Sum.inr v)) := by
    rw [hD]
    simpa [supportSlotVertex] using hreach
  exact ⟨e, (supportSlotVertex_reachable_iff h ext vac (Sum.inl e) (Sum.inr v)).1
    hreach'⟩


/-- Reassembling a vacuum-free external-bearing diagram with an arbitrary quartic complement
has exactly the chosen external-support interaction slots. No connectivity between distinct
external components is assumed. -/
theorem ExternalInsertionDiagram.externallySupportedInteractionPart_ofSlotSplit
    (h : T ⊆ S)
    (ext : ExternalInsertionDiagram ExternalLabel InternalLabel E N T)
    (vac : QuarticDiagram InternalLabel N (S \ T))
    (hext : HasNoVacuumComponent ext.vertexGraph) :
    (ExternalInsertionDiagram.ofSlotSplit h ext vac).externallySupportedInteractionPart = T := by
  classical
  let d := ExternalInsertionDiagram.ofSlotSplit h ext vac
  apply Finset.Subset.antisymm
  · intro v hv
    by_contra hvT
    have hvS : v ∈ S := d.externallySupportedInteractionPart_subset hv
    let vS : ↥S := ⟨v, hvS⟩
    let w : ↥(S \ T) := ⟨v, Finset.mem_sdiff.mpr ⟨hvS, hvT⟩⟩
    obtain ⟨e, he⟩ := (d.mem_externallySupportedInteractionPart vS).1 hv
    have hr : d.vertexGraph.Reachable (Sum.inl e) (Sum.inr vS) :=
      (d.vertexGraph.mem_componentBlock (Sum.inr vS) (Sum.inl e)).1 he
    apply SimpleGraph.not_reachable_sum_inl_inr
      (G := ext.vertexGraph) (H := vac.vertexGraph) (Sum.inl e) w
    apply (SimpleGraph.Iso.reachable_iff
      (φ := supportSlotVertexGraphIso h ext vac)
      (u := Sum.inl (Sum.inl e)) (v := Sum.inr w)).mp
    change d.vertexGraph.Reachable
      (supportSlotVertexEquiv h (Sum.inl (Sum.inl e)))
      (supportSlotVertexEquiv h (Sum.inr w))
    simpa [supportSlotVertexEquiv_inl, supportSlotVertexEquiv_inr,
      supportSlotVertex, vS, w] using hr
  · intro v hv
    let vT : ↥T := ⟨v, hv⟩
    let vS : ↥S := ⟨v, h hv⟩
    obtain ⟨e, he⟩ := hext vT
    have hr : d.vertexGraph.Reachable (Sum.inl e) (Sum.inr vS) := by
      simpa [d, supportSlotVertex] using
        (supportSlotVertex_reachable_iff h ext vac (Sum.inl e) (Sum.inr vT)).2 he
    apply (d.mem_externallySupportedInteractionPart vS).2
    exact ⟨e, (d.vertexGraph.mem_componentBlock (Sum.inr vS) (Sum.inl e)).2 hr⟩

end Common
end SecondQuantization
