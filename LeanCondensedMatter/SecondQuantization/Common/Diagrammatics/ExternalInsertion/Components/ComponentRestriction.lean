import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Core.Diagram
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ComponentLegData
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Core.Diagram
import LeanCondensedMatter.Combinatorics.PerfectPairing.Embedding
import LeanCondensedMatter.Combinatorics.PerfectPairing.Restriction
import LeanCondensedMatter.Combinatorics.InvolutionCard
import LeanCondensedMatter.Combinatorics.FamilySlotShuffle
import LeanCondensedMatter.Combinatorics.FinpartitionProduct
import Mathlib.Data.Finset.Sort

set_option linter.style.header false

/-!
# Restricting components of external-insertion diagrams

This module extracts the external and interaction sectors belonging to one connected component and
restricts the ambient pairing to its legs. The generic restriction is again an
`ExternalInsertionDiagram` on the component-local external and interaction sectors. For a vacuum
component, no external leg is present, so the same ambient component can also be reindexed directly
as the four local legs of an ordinary quartic diagram.

The construction is statistics-independent. Partner-invariant pairing restriction is owned by
`Combinatorics.PerfectPairing.Restriction`, while external/vacuum component predicates are owned by
the shared external-component layer. This module supplies domain-specific leg reindexing and the
canonical family shuffle formed by all component leg embeddings.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*} {E N : ℕ}

/-- A flattened leg belongs to `B` when the component block of its incident vertex is `B`. -/
def ExternalInsertionDiagram.legInComponent {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : Finset (ExternalInsertionVertex E S))
    (leg : Fin (2 * (2 * S.card + E))) : Prop :=
  d.vertexGraph.componentBlock (externalInsertionVertexOfLeg leg) = B

/-- For an actual component-partition part, a leg belongs to the component exactly when its incident
vertex belongs to that part. -/
theorem ExternalInsertionDiagram.legInComponent_iff_vertex_mem {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    {B : Finset (ExternalInsertionVertex E S)} (hB : B ∈ d.vertexGraph.componentPartition.parts)
    (leg : Fin (2 * (2 * S.card + E))) :
    d.legInComponent B leg ↔ externalInsertionVertexOfLeg leg ∈ B := by
  unfold ExternalInsertionDiagram.legInComponent
  exact d.vertexGraph.componentBlock_eq_iff_mem hB (externalInsertionVertexOfLeg leg)

/-- Flattening preserves the component-membership predicate. -/
private theorem ExternalInsertionDiagram.legInComponent_iff_unflattened {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.vertexGraph.componentPartition.parts) (leg : Fin (2 * (2 * S.card + E))) :
    d.legInComponent B leg ↔
      componentLegVertex (externalInsertionLegEquiv E S leg) ∈
        (B : Finset (ExternalInsertionVertex E S)) := by
  rw [d.legInComponent_iff_vertex_mem B.2 leg]
  unfold externalInsertionVertexOfLeg
  cases externalInsertionLegEquiv E S leg <;> rfl

/-- Reindex the flattened legs of one component by its external and interaction data. -/
private noncomputable def ExternalInsertionDiagram.componentBlockLegDataEquiv
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.vertexGraph.componentPartition.parts) :
    {leg : Fin (2 * (2 * S.card + E)) //
      d.legInComponent (B : Finset (ExternalInsertionVertex E S)) leg} ≃
      ↥(Finset.toLeft
        (B : Finset (ExternalInsertionVertex E S))) ⊕
        (↥(interactionSector
          (B : Finset (ExternalInsertionVertex E S))) × Fin 4) :=
  ((externalInsertionLegEquiv E S).subtypeEquiv fun leg =>
      d.legInComponent_iff_unflattened B leg).trans
    (SecondQuantization.Common.componentLegDataEquiv
      (External := Fin (2 * E)) (Vertex := Fin N) (Local := Fin 4)
      (B := (B : Finset (ExternalInsertionVertex E S))))

private theorem ExternalInsertionDiagram.legInComponent_partner_iff {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : Finset (ExternalInsertionVertex E S))
    (leg : Fin (2 * (2 * S.card + E))) :
    d.legInComponent B leg ↔ d.legInComponent B (d.pairing.partner leg) := by
  unfold ExternalInsertionDiagram.legInComponent
  change
    (d.pairing.vertexGraph (externalInsertionVertexOfLeg (E := E))).componentBlock
        (externalInsertionVertexOfLeg leg) = B ↔
      (d.pairing.vertexGraph (externalInsertionVertexOfLeg (E := E))).componentBlock
        (externalInsertionVertexOfLeg (d.pairing.partner leg)) = B
  rw [d.pairing.vertexGraph_componentBlock_partner
    (externalInsertionVertexOfLeg (E := E)) leg]

/-- Every connected component contains an even number of external insertions. -/
theorem ExternalInsertionDiagram.externalSector_card_even {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.vertexGraph.componentPartition.parts) :
    Even (Finset.toLeft
      (B : Finset (ExternalInsertionVertex E S))).card := by
  classical
  let restricted :=
    d.pairing.restrict
      (d.legInComponent (B : Finset (ExternalInsertionVertex E S)))
      (fun leg => d.legInComponent_partner_iff
        (B : Finset (ExternalInsertionVertex E S)) leg)
  have hEven :
      Even (Fintype.card {leg : Fin (2 * (2 * S.card + E)) //
        d.legInComponent (B : Finset (ExternalInsertionVertex E S)) leg}) :=
    restricted.even_card
  simpa only [Fintype.card_coe] using
    externalCardEven_of_equiv_sum_prod (d.componentBlockLegDataEquiv B) hEven (by simpa only [Fintype.card_fin] using (show Even 4 from ⟨2, rfl⟩))

/-- The local external-sector parameter: half the number of one-legged external insertions
carried by one connected component. -/
noncomputable def ExternalInsertionDiagram.externalPairCount {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.vertexGraph.componentPartition.parts) : ℕ :=
  (Finset.toLeft
    (B : Finset (ExternalInsertionVertex E S))).card / 2

/-- The external sector of one component has twice its local external-pair count. -/
private theorem ExternalInsertionDiagram.externalSector_card_eq_two_mul_externalPairCount
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.vertexGraph.componentPartition.parts) :
    (Finset.toLeft
      (B : Finset (ExternalInsertionVertex E S))).card =
      2 * d.externalPairCount B := by
  rw [ExternalInsertionDiagram.externalPairCount]
  exact (Nat.two_mul_div_two_of_even (d.externalSector_card_even B)).symm

/-- Increasing reindexing of a component's ambient external insertions by its local external slots. -/
noncomputable def ExternalInsertionDiagram.externalSectorOrderIso {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.vertexGraph.componentPartition.parts) :
    Fin (2 * d.externalPairCount B) ≃o
      ↥(Finset.toLeft
        (B : Finset (ExternalInsertionVertex E S))) :=
  (Finset.toLeft
    (B : Finset (ExternalInsertionVertex E S))).orderIsoOfFin
      (d.externalSector_card_eq_two_mul_externalPairCount B)

/-- The canonical order-preserving shuffle of component-local external insertions into the
ambient external-insertion order. -/
noncomputable def ExternalInsertionDiagram.componentExternalShuffle
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S) :
    FamilySlotShuffleTo
      (fun B : d.vertexGraph.componentPartition.parts => 2 * d.externalPairCount B)
      (2 * E) where
  slotEquiv :=
    (Equiv.sigmaCongrRight fun B : d.vertexGraph.componentPartition.parts =>
      (d.externalSectorOrderIso B).toEquiv).trans <|
      ((Equiv.subtypeUnivEquiv
        (fun e : Fin (2 * E) => Finset.mem_univ e)).symm.trans <|
        d.vertexGraph.componentPartition.equivSigmaSubfinsets
          (Finset.univ : Finset (Fin (2 * E)))
          (fun e => (Sum.inl (e : Fin (2 * E)) :
            ExternalInsertionVertex E S))
          (fun _ => Finset.mem_univ _)
          (fun B => Finset.toLeft
            (B : Finset (ExternalInsertionVertex E S)))
          (fun _ => Finset.subset_univ _)
          (fun _ _ => Finset.mem_toLeft)).symm
  strictMono := fun B _ _ hef =>
    (d.externalSectorOrderIso B).strictMono hef

@[simp]
theorem ExternalInsertionDiagram.componentExternalShuffle_slotEquiv_apply
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.vertexGraph.componentPartition.parts)
    (e : Fin (2 * d.externalPairCount B)) :
    d.componentExternalShuffle.slotEquiv ⟨B, e⟩ =
      (d.externalSectorOrderIso B e).1 := by
  rfl

/-- Reindex the flattened legs of one component as the flattened legs of its local
external-insertion diagram. -/
private noncomputable def ExternalInsertionDiagram.componentBlockLegEquiv
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.vertexGraph.componentPartition.parts) :
    {leg : Fin (2 * (2 * S.card + E)) //
      d.legInComponent (B : Finset (ExternalInsertionVertex E S)) leg} ≃
      Fin (2 * (2 * (interactionSector
        (B : Finset (ExternalInsertionVertex E S))).card + d.externalPairCount B)) :=
  (d.componentBlockLegDataEquiv B).trans <|
    (Equiv.sumCongr (d.externalSectorOrderIso B).toEquiv (Equiv.refl _)).symm.trans <|
      (externalInsertionLegEquiv (d.externalPairCount B)
        (interactionSector
          (B : Finset (ExternalInsertionVertex E S)))).symm

/-- Restrict one connected component to a standalone external-insertion diagram on its local
external and interaction sectors. -/
noncomputable def ExternalInsertionDiagram.restrictComponent {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.vertexGraph.componentPartition.parts) :
    ExternalInsertionDiagram ExternalLabel InternalLabel (d.externalPairCount B) N
      (interactionSector
        (B : Finset (ExternalInsertionVertex E S))) where
  externalLabel e := d.externalLabel (d.externalSectorOrderIso B e).1
  vertexLabel v :=
    d.vertexLabel ⟨v.1, interactionSector_subset
      (B : Finset (ExternalInsertionVertex E S)) v.2⟩
  pairing :=
    d.pairing.restrictAlongEquiv
      (d.legInComponent (B : Finset (ExternalInsertionVertex E S)))
      (fun leg => d.legInComponent_partner_iff
        (B : Finset (ExternalInsertionVertex E S)) leg)
      (d.componentBlockLegEquiv B)

/-- Embed a flattened leg of a restricted component into the ambient diagram's fixed flattened-leg
enumeration. -/
noncomputable def ExternalInsertionDiagram.componentDiagramLeg {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.vertexGraph.componentPartition.parts) :
    Fin (2 * (2 * (interactionSector
      (B : Finset (ExternalInsertionVertex E S))).card + d.externalPairCount B)) →
      Fin (2 * (2 * S.card + E)) :=
  fun p => ((d.componentBlockLegEquiv B).symm p).1

/-- The restricted component pairing partner, transported back to ambient flattened-leg
coordinates, agrees with the ambient pairing partner. -/
theorem ExternalInsertionDiagram.componentDiagramLeg_restrictComponent_pairing_partner
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.vertexGraph.componentPartition.parts)
    (p : Fin (2 * (2 * (interactionSector
      (B : Finset (ExternalInsertionVertex E S))).card + d.externalPairCount B))) :
    d.componentDiagramLeg B ((d.restrictComponent B).pairing.partner p) =
      d.pairing.partner (d.componentDiagramLeg B p) := by
  simpa [ExternalInsertionDiagram.componentDiagramLeg,
    ExternalInsertionDiagram.restrictComponent] using
    d.pairing.restrictAlongEquiv_partner_symm_val
      (d.legInComponent (B : Finset (ExternalInsertionVertex E S)))
      (fun i => d.legInComponent_partner_iff
        (B : Finset (ExternalInsertionVertex E S)) i)
      (d.componentBlockLegEquiv B) p

/-- On an external slot, the component leg embedding is the ambient external slot selected by
the component's increasing external-sector order. -/
@[simp]
theorem ExternalInsertionDiagram.componentDiagramLeg_external
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.vertexGraph.componentPartition.parts) (e : Fin (2 * d.externalPairCount B)) :
    d.componentDiagramLeg B
        (externalInsertionExternalLeg (d.externalPairCount B)
          (interactionSector
            (B : Finset (ExternalInsertionVertex E S))) e) =
      externalInsertionExternalLeg E S (d.externalSectorOrderIso B e).1 := by
  simp [ExternalInsertionDiagram.componentDiagramLeg,
    ExternalInsertionDiagram.componentBlockLegEquiv,
    ExternalInsertionDiagram.componentBlockLegDataEquiv,
    componentLegDataEquiv,
    externalInsertionExternalLeg, externalInsertionInteractionLeg]

/-- On an interaction slot, the component leg embedding is the corresponding ambient interaction
vertex and local quartic leg. -/
@[simp]
theorem ExternalInsertionDiagram.componentDiagramLeg_interaction
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.vertexGraph.componentPartition.parts)
    (v : ↥(interactionSector
      (B : Finset (ExternalInsertionVertex E S)))) (l : Fin 4) :
    d.componentDiagramLeg B
        (externalInsertionInteractionLeg (E := d.externalPairCount B) v l) =
      externalInsertionInteractionLeg (E := E)
        ⟨v.1, interactionSector_subset
          (B : Finset (ExternalInsertionVertex E S)) v.2⟩ l := by
  simp [ExternalInsertionDiagram.componentDiagramLeg,
    ExternalInsertionDiagram.componentBlockLegEquiv,
    ExternalInsertionDiagram.componentBlockLegDataEquiv,
    componentLegDataEquiv,
    externalInsertionExternalLeg, externalInsertionInteractionLeg]

/-- The component-local flattened-leg embedding preserves the canonical external-insertion leg
order. -/
private theorem ExternalInsertionDiagram.componentDiagramLeg_strictMono
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.vertexGraph.componentPartition.parts) :
    StrictMono (d.componentDiagramLeg B) := by
  let T :=
    interactionSector
      (B : Finset (ExternalInsertionVertex E S))
  let localEquiv := externalInsertionLegEquiv (d.externalPairCount B) T
  intro a b hab
  let la := localEquiv a
  let lb := localEquiv b
  have ha : localEquiv.symm la = a := by simp [la]
  have hb : localEquiv.symm lb = b := by simp [lb]
  rw [← ha, ← hb] at hab ⊢
  rcases la with e | ⟨v, l⟩ <;> rcases lb with f | ⟨w, k⟩
  · change
      (externalInsertionExternalLeg (d.externalPairCount B) T e).val <
        (externalInsertionExternalLeg (d.externalPairCount B) T f).val at hab
    change d.componentDiagramLeg B
        (externalInsertionExternalLeg (d.externalPairCount B) T e) <
      d.componentDiagramLeg B
        (externalInsertionExternalLeg (d.externalPairCount B) T f)
    rw [d.componentDiagramLeg_external B, d.componentDiagramLeg_external B]
    change
      (externalInsertionExternalLeg E S (d.externalSectorOrderIso B e).1).val <
        (externalInsertionExternalLeg E S (d.externalSectorOrderIso B f).1).val
    have hef : e < f := by
      simpa using hab
    simpa using (d.externalSectorOrderIso B).strictMono hef
  · change d.componentDiagramLeg B
        (externalInsertionExternalLeg (d.externalPairCount B) T e) <
      d.componentDiagramLeg B
        (externalInsertionInteractionLeg (E := d.externalPairCount B) w k)
    rw [d.componentDiagramLeg_external B, d.componentDiagramLeg_interaction B]
    change
      (externalInsertionExternalLeg E S (d.externalSectorOrderIso B e).1).val <
        (externalInsertionInteractionLeg (E := E)
          ⟨w.1, interactionSector_subset
            (B : Finset (ExternalInsertionVertex E S)) w.2⟩ k).val
    simp only [externalInsertionExternalLeg_val, externalInsertionInteractionLeg_val]
    have hbound := (d.externalSectorOrderIso B e).1.isLt
    omega
  · change
      externalInsertionInteractionLeg (E := d.externalPairCount B) v l <
        externalInsertionExternalLeg (d.externalPairCount B) T f at hab
    change
      (externalInsertionInteractionLeg (E := d.externalPairCount B) v l).val <
        (externalInsertionExternalLeg (d.externalPairCount B) T f).val at hab
    simp at hab
    omega
  · change
      externalInsertionInteractionLeg (E := d.externalPairCount B) v l <
        externalInsertionInteractionLeg (E := d.externalPairCount B) w k at hab
    change
      d.componentDiagramLeg B
          (externalInsertionInteractionLeg (E := d.externalPairCount B) v l) <
        d.componentDiagramLeg B
          (externalInsertionInteractionLeg (E := d.externalPairCount B) w k)
    rw [d.componentDiagramLeg_interaction B, d.componentDiagramLeg_interaction B]
    change
      (externalInsertionInteractionLeg (E := E)
        ⟨v.1, interactionSector_subset
          (B : Finset (ExternalInsertionVertex E S)) v.2⟩ l).val <
        (externalInsertionInteractionLeg (E := E)
          ⟨w.1, interactionSector_subset
            (B : Finset (ExternalInsertionVertex E S)) w.2⟩ k).val
    change
      (externalInsertionInteractionLeg (E := d.externalPairCount B) v l).val <
        (externalInsertionInteractionLeg (E := d.externalPairCount B) w k).val at hab
    simp only [externalInsertionInteractionLeg_val] at hab ⊢
    by_cases hvw : v = w
    · subst w
      omega
    · have hrank_ne :
          ((T.orderIsoOfFin rfl).symm v).val ≠
            ((T.orderIsoOfFin rfl).symm w).val := by
        intro h
        apply hvw
        exact (T.orderIsoOfFin rfl).symm.injective (Fin.ext h)
      have hrank :
          ((T.orderIsoOfFin rfl).symm v).val <
            ((T.orderIsoOfFin rfl).symm w).val := by
        have hl := l.isLt
        have hk := k.isLt
        omega
      have hvwT : v < w := by
        simpa using (T.orderIsoOfFin rfl).strictMono hrank
      have hamb :
          ((S.orderIsoOfFin rfl).symm
            (⟨v.1, interactionSector_subset
              (B : Finset (ExternalInsertionVertex E S)) v.2⟩ : ↥S)).val <
          ((S.orderIsoOfFin rfl).symm
            (⟨w.1, interactionSector_subset
              (B : Finset (ExternalInsertionVertex E S)) w.2⟩ : ↥S)).val := by
        apply (S.orderIsoOfFin rfl).symm.strictMono
        change v.1 < w.1
        exact hvwT
      have hl := l.isLt
      have hk := k.isLt
      omega

/-- The canonical order embedding of one restricted component's flattened legs into the ambient
external-insertion leg order. -/
noncomputable def ExternalInsertionDiagram.componentDiagramLegOrderEmbedding
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.vertexGraph.componentPartition.parts) :
    Fin (2 * (2 * (interactionSector
      (B : Finset (ExternalInsertionVertex E S))).card + d.externalPairCount B)) ↪o
      Fin (2 * (2 * S.card + E)) :=
  OrderEmbedding.ofStrictMono (d.componentDiagramLeg B)
    (d.componentDiagramLeg_strictMono B)


/-- The image of the canonical component leg embedding is exactly the ambient legs incident to that
connected component. -/
private theorem ExternalInsertionDiagram.exists_componentDiagramLeg_eq_iff
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.vertexGraph.componentPartition.parts)
    (leg : Fin (2 * (2 * S.card + E))) :
    (∃ p, d.componentDiagramLeg B p = leg) ↔
      d.legInComponent (B : Finset (ExternalInsertionVertex E S)) leg := by
  constructor
  · rintro ⟨p, rfl⟩
    exact ((d.componentBlockLegEquiv B).symm p).2
  · intro hleg
    let leg' :
        {leg : Fin (2 * (2 * S.card + E)) //
          d.legInComponent (B : Finset (ExternalInsertionVertex E S)) leg} :=
      ⟨leg, hleg⟩
    refine ⟨d.componentBlockLegEquiv B leg', ?_⟩
    simp [ExternalInsertionDiagram.componentDiagramLeg, leg']


/-- The component-local leg embeddings, taken over every connected component, form the canonical
order-preserving family shuffle onto the full ambient flattened-leg enumeration. -/
noncomputable def ExternalInsertionDiagram.componentLegShuffle
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S) :
    FamilySlotShuffleTo
      (fun B : d.vertexGraph.componentPartition.parts =>
        2 * (2 * (interactionSector
          (B : Finset (ExternalInsertionVertex E S))).card + d.externalPairCount B))
      (2 * (2 * S.card + E)) where
  slotEquiv :=
    Equiv.ofBijective
      (fun x => d.componentDiagramLeg x.1 x.2)
      (by
        constructor
        · rintro ⟨B, p⟩ ⟨C, q⟩ h
          have hpB :
              d.legInComponent (B : Finset (ExternalInsertionVertex E S))
                (d.componentDiagramLeg B p) :=
            (d.exists_componentDiagramLeg_eq_iff B _).1 ⟨p, rfl⟩
          have hqC :
              d.legInComponent (C : Finset (ExternalInsertionVertex E S))
                (d.componentDiagramLeg C q) :=
            (d.exists_componentDiagramLeg_eq_iff C _).1 ⟨q, rfl⟩
          have hpC :
              d.legInComponent (C : Finset (ExternalInsertionVertex E S))
                (d.componentDiagramLeg B p) := by
            simpa only [h] using hqC
          have hBCval :
              (B : Finset (ExternalInsertionVertex E S)) =
                (C : Finset (ExternalInsertionVertex E S)) := by
            unfold ExternalInsertionDiagram.legInComponent at hpB hpC
            exact hpB.symm.trans hpC
          have hBC : B = C := Subtype.ext hBCval
          subst C
          have hpq : p = q :=
            (d.componentDiagramLegOrderEmbedding B).injective h
          subst q
          rfl
        · intro leg
          let B : d.vertexGraph.componentPartition.parts :=
            ⟨d.vertexGraph.componentBlock (externalInsertionVertexOfLeg leg),
              d.vertexGraph.componentBlock_mem_componentPartition
                (externalInsertionVertexOfLeg leg)⟩
          have hleg :
              d.legInComponent (B : Finset (ExternalInsertionVertex E S)) leg := by
            rfl
          obtain ⟨p, hp⟩ := (d.exists_componentDiagramLeg_eq_iff B leg).2 hleg
          exact ⟨⟨B, p⟩, hp⟩)
  strictMono := fun B => (d.componentDiagramLegOrderEmbedding B).strictMono

@[simp]
theorem ExternalInsertionDiagram.componentLegShuffle_slotEquiv_apply
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.vertexGraph.componentPartition.parts)
    (p : Fin (2 * (2 * (interactionSector
      (B : Finset (ExternalInsertionVertex E S))).card + d.externalPairCount B))) :
    d.componentLegShuffle.slotEquiv ⟨B, p⟩ = d.componentDiagramLeg B p :=
  rfl


/-- Restrict a vacuum component of an external-insertion diagram to an ordinary quartic diagram. -/
noncomputable def ExternalInsertionDiagram.restrictVacuumComponent {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.vertexGraph.componentPartition.parts)
    (hVac : ComponentIsVacuum (B : Finset (ExternalInsertionVertex E S))) :
    QuarticDiagram InternalLabel N
      (interactionSector
        (B : Finset (ExternalInsertionVertex E S))) where
  vertexLabel v :=
    d.vertexLabel ⟨v.1, interactionSector_subset
      (B : Finset (ExternalInsertionVertex E S)) v.2⟩
  pairing := by
    let legEquiv :
        {leg : Fin (2 * (2 * S.card + E)) // d.legInComponent B leg} ≃
          Fin (2 * (2 * (interactionSector
            (B : Finset (ExternalInsertionVertex E S))).card)) :=
      ((externalInsertionLegEquiv E S).subtypeEquiv fun leg =>
          d.legInComponent_iff_unflattened B leg).trans
        ((SecondQuantization.Common.vacuumComponentLegDataEquiv
          (External := Fin (2 * E)) (Vertex := Fin N) (Local := Fin 4)
          (B := (B : Finset (ExternalInsertionVertex E S))) hVac).trans
          (quarticLegEquiv (interactionSector
            (B : Finset (ExternalInsertionVertex E S)))).symm)
    exact d.pairing.restrictAlongEquiv (d.legInComponent B)
      (fun leg => d.legInComponent_partner_iff
        (B : Finset (ExternalInsertionVertex E S)) leg)
      legEquiv

end Common
end SecondQuantization
