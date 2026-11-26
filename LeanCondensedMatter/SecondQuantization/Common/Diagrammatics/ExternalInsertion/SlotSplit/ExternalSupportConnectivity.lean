import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.SlotSplit.ExternalSupportDecomposition
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Core.Connected
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.InteractionSector

set_option linter.style.header false

/-!
# Vacuum-freeness of the external-bearing diagram

The slot splitting preserves and reflects reachability between vertices on its external-bearing
side. Hence restricting a diagram to all components meeting the external sector leaves no vacuum
components, without requiring distinct external vertices to be mutually connected.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*} {E N : ℕ}
  {S T : Finset (Fin N)}

/-- The external-bearing and vacuum vertex sectors partition the ambient vertices. -/
noncomputable def supportSlotVertexEquiv (h : T ⊆ S) :
    (ExternalInsertionVertex E T ⊕ ↥(S \ T)) ≃ ExternalInsertionVertex E S :=
  (Equiv.sumAssoc (Fin (2 * E)) ↥T ↥(S \ T)).trans
    (Equiv.sumCongr (Equiv.refl (Fin (2 * E))) (subsetSumSdiffEquiv h))

/-- The external-bearing vertex inclusion leaves external vertices unchanged and
includes retained interaction vertices in the ambient slot set. -/
@[simp]
theorem supportSlotVertexEquiv_inl (h : T ⊆ S) (x : ExternalInsertionVertex E T) :
    supportSlotVertexEquiv h (Sum.inl x) =
      (match x with
      | Sum.inl e => Sum.inl e
      | Sum.inr v => Sum.inr ⟨v.1, h v.2⟩) := by
  cases x with
  | inl e => rfl
  | inr v =>
      change (Sum.inr (subsetSumSdiffEquiv h (Sum.inl v)) : ExternalInsertionVertex E S) = _
      rw [subsetSumSdiffEquiv_inl_apply]

/-- Left legs retain the corresponding vertices under the splitting. -/
private theorem supportSlotVertex_of_left_leg (h : T ⊆ S)
    (i : Fin (2 * (2 * T.card + E))) :
    externalInsertionVertexOfLeg
        (externalInsertionSlotLegSplitting (E := E) h (Sum.inl i)) =
      supportSlotVertexEquiv h (Sum.inl (externalInsertionVertexOfLeg i)) := by
  obtain ⟨x, rfl⟩ := (externalInsertionLegEquiv E T).symm.surjective i
  cases x with
  | inl e =>
      rw [externalInsertionSlotLegSplitting_external]
      simp [externalInsertionVertexOfLeg, supportSlotVertexEquiv]
  | inr p =>
      obtain ⟨v, l⟩ := p
      rw [externalInsertionSlotLegSplitting_left_interaction]
      simp [externalInsertionVertexOfLeg, supportSlotVertexEquiv]

/-- Right legs retain the corresponding quartic vertices under the splitting. -/
private theorem supportSlotVertex_of_right_leg (h : T ⊆ S)
    (i : Fin (2 * (2 * (S \ T).card))) :
    externalInsertionVertexOfLeg
        (externalInsertionSlotLegSplitting (E := E) h (Sum.inr i)) =
      supportSlotVertexEquiv (E := E) h (Sum.inr (vertexOfLeg i)) := by
  change
    externalInsertionVertexOfLeg
        (externalInsertionSlotLegSplitting (E := E) h (Sum.inr i)) =
      (Sum.inr (subsetSumSdiffEquiv h (Sum.inr (vertexOfLeg i))) :
        ExternalInsertionVertex E S)
  rw [subsetSumSdiffEquiv_inr_apply]
  obtain ⟨p, rfl⟩ := (quarticLegEquiv (S \ T)).symm.surjective i
  obtain ⟨v, l⟩ := p
  rw [externalInsertionSlotLegSplitting_right_interaction]
  simp [externalInsertionVertexOfLeg, vertexOfLeg]

variable (h : T ⊆ S)
    (ext : ExternalInsertionDiagram ExternalLabel InternalLabel E N T)
    (vac : QuarticDiagram InternalLabel N (S \ T))

/-- A split external-insertion diagram has the disjoint sum of its external-bearing
and vacuum vertex graphs. -/
noncomputable def supportSlotVertexGraphIso :
    (ext.vertexGraph ⊕g vac.vertexGraph) ≃g
      (ExternalInsertionDiagram.ofSlotSplit h ext vac).vertexGraph :=
  Pairing.vertexGraphOfSplitIso (externalInsertionSlotLegSplitting (E := E) h)
    ext.pairing vac.pairing
    (externalInsertionVertexOfLeg (E := E) (S := T)) (vertexOfLeg (S := S \ T))
    (supportSlotVertexEquiv h) (externalInsertionVertexOfLeg (E := E) (S := S))
    (by
      intro i
      exact supportSlotVertex_of_left_leg h i)
    (by
      intro i
      exact supportSlotVertex_of_right_leg h i)

/-- Reachability in the external-bearing piece is reflected by the disjoint graph sum. -/
private theorem supportSlotVertex_reachable_iff (x y : ExternalInsertionVertex E T) :
    (ExternalInsertionDiagram.ofSlotSplit h ext vac).vertexGraph.Reachable
        (supportSlotVertexEquiv h (Sum.inl x))
        (supportSlotVertexEquiv h (Sum.inl y)) ↔
      ext.vertexGraph.Reachable x y := by
  change (ExternalInsertionDiagram.ofSlotSplit h ext vac).vertexGraph.Reachable
      ((supportSlotVertexGraphIso h ext vac) (Sum.inl x))
      ((supportSlotVertexGraphIso h ext vac) (Sum.inl y)) ↔ _
  simp only [SimpleGraph.Iso.reachable_iff, SimpleGraph.reachable_sum_inl_iff]

/-- The canonical external-bearing diagram contains no pure-vacuum connected components.
All components touching distinct external insertions are retained independently. -/
theorem ExternalInsertionDiagram.hasNoVacuumComponent_externalBearingDiagram
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S) :
    HasNoVacuumComponent d.externalBearingDiagram.vertexGraph := by
  classical
  intro v
  let T := d.externallySupportedInteractionPart
  let h : T ⊆ S := d.externallySupportedInteractionPart_subset
  let ext := d.externalBearingDiagram
  let vac := d.vacuumDiagram
  let vS : ↥S := ⟨v.1, h v.2⟩
  obtain ⟨e, he⟩ := (d.mem_externallySupportedInteractionPart vS).1 v.2
  have hreach : d.vertexGraph.Reachable (Sum.inl e) (Sum.inr vS) :=
    (d.vertexGraph.mem_componentBlock (Sum.inr vS) (Sum.inl e)).1 he
  refine ⟨e, ?_⟩
  apply (supportSlotVertex_reachable_iff h ext vac (Sum.inl e) (Sum.inr v)).1
  rw [d.externalBearing_vacuum_reconstruction]
  simpa [supportSlotVertexEquiv] using hreach


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
    simpa [supportSlotVertexEquiv, vS, w] using hr
  · intro v hv
    let vT : ↥T := ⟨v, hv⟩
    let vS : ↥S := ⟨v, h hv⟩
    obtain ⟨e, he⟩ := hext vT
    have hr : d.vertexGraph.Reachable (Sum.inl e) (Sum.inr vS) := by
      simpa [d, supportSlotVertexEquiv] using
        (supportSlotVertex_reachable_iff h ext vac (Sum.inl e) (Sum.inr vT)).2 he
    apply (d.mem_externallySupportedInteractionPart vS).2
    exact ⟨e, (d.vertexGraph.mem_componentBlock (Sum.inr vS) (Sum.inl e)).2 hr⟩

/-- The inclusion of a quartic vacuum vertex into the ambient interaction sector. -/
def supportSlotVacuumVertex (v : ↥(S \ T)) :
    ExternalInsertionVertex E S :=
  Sum.inr ⟨v.1, (Finset.mem_sdiff.mp v.2).1⟩

/-- The graph-sum isomorphism identifies vacuum-side reachability with reachability in the
quartic vacuum graph. -/
private theorem reachable_ofSlotSplitVacuum_iff (x y : ↥(S \ T)) :
    (ExternalInsertionDiagram.ofSlotSplit h ext vac).vertexGraph.Reachable
      (supportSlotVacuumVertex (E := E) x) (supportSlotVacuumVertex (E := E) y) ↔
      vac.vertexGraph.Reachable x y := by
  change (ExternalInsertionDiagram.ofSlotSplit h ext vac).vertexGraph.Reachable
      ((supportSlotVertexGraphIso h ext vac) (Sum.inr x))
      ((supportSlotVertexGraphIso h ext vac) (Sum.inr y)) ↔ _
  simp only [SimpleGraph.Iso.reachable_iff, SimpleGraph.reachable_sum_inr_iff]

/-- The interaction vertices in the ambient component generated by one vacuum-piece vertex are
exactly that vertex's connected component in the quartic vacuum piece. -/
theorem interactionSector_componentBlock_slotSplitVacuumVertex (v : ↥(S \ T)) :
    interactionSector
        ((ExternalInsertionDiagram.ofSlotSplit h ext vac).vertexGraph.componentBlock
          (supportSlotVacuumVertex (E := E) v)) =
      vac.vertexGraph.componentBlockOn v := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxS, hxBlock⟩ := (mem_interactionSector _ x).1 hx
    have hreach :
        (ExternalInsertionDiagram.ofSlotSplit h ext vac).vertexGraph.Reachable
          (supportSlotVacuumVertex (E := E) v) (Sum.inr ⟨x, hxS⟩) :=
      (((ExternalInsertionDiagram.ofSlotSplit h ext vac).vertexGraph.mem_componentBlock
        (supportSlotVacuumVertex (E := E) v) (Sum.inr ⟨x, hxS⟩)).1 hxBlock).symm
    by_cases hxT : x ∈ T
    · have hsum :
          (ext.vertexGraph ⊕g vac.vertexGraph).Reachable
            (Sum.inr v) (Sum.inl (Sum.inr ⟨x, hxT⟩)) :=
        (SimpleGraph.Iso.reachable_iff
          (φ := supportSlotVertexGraphIso h ext vac)
          (u := Sum.inr v) (v := Sum.inl (Sum.inr ⟨x, hxT⟩))).mp
          (by
            change (ExternalInsertionDiagram.ofSlotSplit h ext vac).vertexGraph.Reachable
              (supportSlotVacuumVertex (E := E) v) (supportSlotVertexEquiv h (Sum.inl (Sum.inr ⟨x, hxT⟩)))
            simpa [supportSlotVertexEquiv] using hreach)
      exact False.elim (SimpleGraph.not_reachable_sum_inl_inr _ _ hsum.symm)
    · let y : ↥(S \ T) := ⟨x, Finset.mem_sdiff.mpr ⟨hxS, hxT⟩⟩
      exact (vac.vertexGraph.mem_componentBlockOn v).2
        ⟨y.2, (reachable_ofSlotSplitVacuum_iff h ext vac y v).1 (by
          change (ExternalInsertionDiagram.ofSlotSplit h ext vac).vertexGraph.Reachable
            (Sum.inr ⟨x, hxS⟩) (supportSlotVacuumVertex (E := E) v)
          exact hreach.symm)⟩
  · intro hx
    obtain ⟨hxST, hreach⟩ := (vac.vertexGraph.mem_componentBlockOn v).1 hx
    let y : ↥(S \ T) := ⟨x, hxST⟩
    apply (mem_interactionSector _ x).2
    refine ⟨(Finset.mem_sdiff.mp hxST).1, ?_⟩
    apply ((ExternalInsertionDiagram.ofSlotSplit h ext vac).vertexGraph.mem_componentBlock
      (supportSlotVacuumVertex (E := E) v) (Sum.inr ⟨x, (Finset.mem_sdiff.mp hxST).1⟩)).2
    simpa [y, supportSlotVacuumVertex] using
      (reachable_ofSlotSplitVacuum_iff h ext vac y v).2 hreach

/-- A component generated by a vertex of the quartic right side is a vacuum component of the
reassembled external-insertion diagram. -/
theorem componentBlock_slotSplitVacuumVertex_mem_vacuumComponentParts
    (v : ↥(S \ T)) :
    let d := ExternalInsertionDiagram.ofSlotSplit h ext vac
    let B : d.vertexGraph.componentPartition.parts :=
      ⟨d.vertexGraph.componentBlock (supportSlotVacuumVertex (E := E) v),
        d.vertexGraph.componentBlock_mem_componentPartition (supportSlotVacuumVertex (E := E) v)⟩
    B ∈ (vacuumComponentParts d.vertexGraph) := by
  dsimp only
  rw [mem_vacuumComponentParts]
  unfold ComponentIsVacuum ComponentMeetsExternal
  rintro ⟨e, he⟩
  have hreach :
      (ExternalInsertionDiagram.ofSlotSplit h ext vac).vertexGraph.Reachable
        (Sum.inl e) (supportSlotVacuumVertex (E := E) v) :=
    ((ExternalInsertionDiagram.ofSlotSplit h ext vac).vertexGraph.mem_componentBlock
      (supportSlotVacuumVertex (E := E) v) (Sum.inl e)).1 he
  have hsum :
      (ext.vertexGraph ⊕g vac.vertexGraph).Reachable
        (Sum.inl (Sum.inl e)) (Sum.inr v) :=
    (SimpleGraph.Iso.reachable_iff
      (φ := supportSlotVertexGraphIso h ext vac)
      (u := Sum.inl (Sum.inl e)) (v := Sum.inr v)).mp
      (by
        change (ExternalInsertionDiagram.ofSlotSplit h ext vac).vertexGraph.Reachable
          (supportSlotVertexEquiv h (Sum.inl (Sum.inl e))) (supportSlotVacuumVertex (E := E) v)
        simpa [supportSlotVertexEquiv] using hreach)
  exact SimpleGraph.not_reachable_sum_inl_inr _ _ hsum

/-- Every leg in a vacuum component lies on the quartic side of the slot split
when the external-bearing piece has no vacuum components. -/
theorem ExternalInsertionDiagram.ofSlotSplit_vacuumLeg_mem_right
    (hext : HasNoVacuumComponent ext.vertexGraph)
    (i : Fin (2 * (2 * S.card + E)))
    (hVac : ComponentIsVacuum
      ((ExternalInsertionDiagram.ofSlotSplit h ext vac).vertexGraph.componentBlock
        (externalInsertionVertexOfLeg i))) :
    ∃ q : Fin (2 * (2 * (S \ T).card)),
      externalInsertionSlotLegSplitting (E := E) h (Sum.inr q) = i := by
  classical
  let d := ExternalInsertionDiagram.ofSlotSplit h ext vac
  let split := externalInsertionSlotLegSplitting (E := E) h
  have hi : split (split.symm i) = i := split.apply_symm_apply i
  cases hside : split.symm i with
  | inl p =>
      have hv : externalInsertionVertexOfLeg (E := E) i =
          supportSlotVertexEquiv h (Sum.inl (externalInsertionVertexOfLeg p)) := by
        rw [← hi, hside]
        exact supportSlotVertex_of_left_leg h p
      have hleft : ∃ e : Fin (2 * E), ext.vertexGraph.Reachable
          (Sum.inl e) (externalInsertionVertexOfLeg p) := by
        cases hx : externalInsertionVertexOfLeg (E := E) (S := T) p with
        | inl e => exact ⟨e, SimpleGraph.Reachable.refl _⟩
        | inr v => exact hext v
      obtain ⟨e, he⟩ := hleft
      apply False.elim
      apply hVac
      refine ⟨e, ?_⟩
      apply (d.vertexGraph.mem_componentBlock _ (Sum.inl e)).2
      rw [hv]
      simpa [supportSlotVertexEquiv] using
        (supportSlotVertex_reachable_iff h ext vac (Sum.inl e)
          (externalInsertionVertexOfLeg p)).2 he
  | inr q =>
      exact ⟨q, by rw [hside] at hi; exact hi⟩

/-- Send a quartic vacuum-piece component to the corresponding ambient vacuum component. -/
noncomputable def slotSplitVacuumComponentPart
    (C : vac.vertexGraph.componentPartitionOn.parts) :
    ↥(vacuumComponentParts (ExternalInsertionDiagram.ofSlotSplit h ext vac).vertexGraph) :=
  let v : ↥(S \ T) :=
    ⟨Classical.choose (vac.vertexGraph.componentPartitionOn.part_surjOn C.2),
      (Classical.choose_spec (vac.vertexGraph.componentPartitionOn.part_surjOn C.2)).1⟩
  let d := ExternalInsertionDiagram.ofSlotSplit h ext vac
  let B : d.vertexGraph.componentPartition.parts :=
    ⟨d.vertexGraph.componentBlock (supportSlotVacuumVertex (E := E) v),
      d.vertexGraph.componentBlock_mem_componentPartition (supportSlotVacuumVertex (E := E) v)⟩
  ⟨B, componentBlock_slotSplitVacuumVertex_mem_vacuumComponentParts h ext vac v⟩

/-- The ambient interaction part of the image component is exactly the original quartic component. -/
theorem interactionSector_slotSplitVacuumComponentPart
    (C : vac.vertexGraph.componentPartitionOn.parts) :
    interactionSector
        ((slotSplitVacuumComponentPart h ext vac C).1.1 :
          Finset (ExternalInsertionVertex E S)) =
      (C : Finset (Fin N)) := by
  let v : ↥(S \ T) :=
    ⟨Classical.choose (vac.vertexGraph.componentPartitionOn.part_surjOn C.2),
      (Classical.choose_spec (vac.vertexGraph.componentPartitionOn.part_surjOn C.2)).1⟩
  change interactionSector
      ((ExternalInsertionDiagram.ofSlotSplit h ext vac).vertexGraph.componentBlock
        (supportSlotVacuumVertex (E := E) v)) = _
  rw [interactionSector_componentBlock_slotSplitVacuumVertex]
  change vac.vertexGraph.componentPartitionOn.part
    (Classical.choose (vac.vertexGraph.componentPartitionOn.part_surjOn C.2)) = _
  exact (Classical.choose_spec (vac.vertexGraph.componentPartitionOn.part_surjOn C.2)).2

/-- The quartic-to-ambient vacuum component map is injective. -/
private theorem slotSplitVacuumComponentPart_injective :
    Function.Injective (slotSplitVacuumComponentPart h ext vac) := by
  intro C D hCD
  apply Subtype.ext
  have hparts := congrArg (fun B => B.1.1) hCD
  have hint := congrArg interactionSector hparts
  rw [interactionSector_slotSplitVacuumComponentPart,
    interactionSector_slotSplitVacuumComponentPart] at hint
  exact hint

/-- If the external piece is vacuum-free, an interaction vertex in an ambient vacuum
component must lie on the quartic right side. -/
private theorem not_mem_left_of_mem_vacuumComponentPart
    (hext : HasNoVacuumComponent ext.vertexGraph)
    (B : ↥(vacuumComponentParts (ExternalInsertionDiagram.ofSlotSplit h ext vac).vertexGraph))
    (w : ↥S) (hwB : (Sum.inr w : ExternalInsertionVertex E S) ∈ (B.1 : Finset (ExternalInsertionVertex E S))) :
    (w : Fin N) ∉ T := by
  intro hwT
  let d := ExternalInsertionDiagram.ofSlotSplit h ext vac
  have hm : w.1 ∈ d.externallySupportedInteractionPart := by
    rw [ExternalInsertionDiagram.externallySupportedInteractionPart_ofSlotSplit h ext vac hext]
    exact hwT
  have hmeet := (d.mem_externallySupportedInteractionPart w).1 hm
  have hBlocks : B.1.1 = d.vertexGraph.componentBlock (Sum.inr w) :=
    ((d.vertexGraph.componentBlock_eq_iff_mem B.1.2 _).2 hwB).symm
  exact ((mem_vacuumComponentParts d.vertexGraph B.1).1 B.2)
    (by rw [hBlocks]; exact hmeet)

/-- With a vacuum-free left piece, every ambient vacuum component comes from a quartic
right-side component. -/
private theorem slotSplitVacuumComponentPart_surjective
    (hext : HasNoVacuumComponent ext.vertexGraph) :
    Function.Surjective (slotSplitVacuumComponentPart h ext vac) := by
  intro B
  obtain ⟨x, hxB⟩ :=
    (ExternalInsertionDiagram.ofSlotSplit h ext vac).vertexGraph.componentPartition.nonempty_of_mem_parts B.1.2
  cases x with
  | inl e =>
      have hVac :
          ComponentIsVacuum (B.1 : Finset (ExternalInsertionVertex E S)) :=
        (mem_vacuumComponentParts (ExternalInsertionDiagram.ofSlotSplit h ext vac).vertexGraph B.1).1 B.2
      exact False.elim (hVac ⟨e, hxB⟩)
  | inr w =>
      have hwNot : (w : Fin N) ∉ T :=
        not_mem_left_of_mem_vacuumComponentPart h ext vac hext B w hxB
      let v : ↥(S \ T) := ⟨w.1, Finset.mem_sdiff.mpr ⟨w.2, hwNot⟩⟩
      let C : vac.vertexGraph.componentPartitionOn.parts :=
        ⟨vac.vertexGraph.componentBlockOn v, by
          unfold SimpleGraph.componentBlockOn
          exact vac.vertexGraph.componentPartitionOn.part_mem.2 v.2⟩
      refine ⟨C, ?_⟩
      apply Subtype.ext
      apply interactionSector_component_unique
        (ExternalInsertionDiagram.ofSlotSplit h ext vac).vertexGraph w
      · rw [interactionSector_slotSplitVacuumComponentPart]
        change (w : Fin N) ∈ vac.vertexGraph.componentPartitionOn.part (v : Fin N)
        exact vac.vertexGraph.componentPartitionOn.mem_part v.2
      · exact (mem_interactionSector_subtype
          (B.1 : Finset (ExternalInsertionVertex E S)) w).2 hxB

/-- Connected components of the quartic vacuum piece are equivalent to vacuum components of the
reassembled external-insertion diagram when the external piece is vacuum-free. -/
noncomputable def slotSplitVacuumComponentEquiv
    (hext : HasNoVacuumComponent ext.vertexGraph) :
    vac.vertexGraph.componentPartitionOn.parts ≃
      ↥(vacuumComponentParts (ExternalInsertionDiagram.ofSlotSplit h ext vac).vertexGraph) :=
  Equiv.ofBijective (slotSplitVacuumComponentPart h ext vac)
    ⟨slotSplitVacuumComponentPart_injective h ext vac,
      slotSplitVacuumComponentPart_surjective h ext vac hext⟩

@[simp]
theorem slotSplitVacuumComponentEquiv_apply
    (hext : HasNoVacuumComponent ext.vertexGraph) (C : vac.vertexGraph.componentPartitionOn.parts) :
    slotSplitVacuumComponentEquiv h ext vac hext C =
      slotSplitVacuumComponentPart h ext vac C :=
  rfl


end Common
end SecondQuantization
