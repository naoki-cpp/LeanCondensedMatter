import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Components.ComponentPartition
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.InteractionSector
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
`Combinatorics.PerfectPairing.Restriction`; this module supplies the external-insertion component
predicate, domain-specific leg reindexing, and the canonical family shuffle formed by all component
leg embeddings.
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
  d.componentBlock (externalInsertionVertexOfLeg leg) = B

/-- For an actual component-partition part, a leg belongs to the component exactly when its incident
vertex belongs to that part. -/
theorem ExternalInsertionDiagram.legInComponent_iff_vertex_mem {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    {B : Finset (ExternalInsertionVertex E S)} (hB : B ∈ d.componentPartition.parts)
    (leg : Fin (2 * (2 * S.card + E))) :
    d.legInComponent B leg ↔ externalInsertionVertexOfLeg leg ∈ B := by
  unfold ExternalInsertionDiagram.legInComponent ExternalInsertionDiagram.componentBlock
  apply d.vertexGraph.componentBlock_eq_iff_mem
  simpa only [ExternalInsertionDiagram.componentPartition] using hB

/-- Membership of an unflattened leg in a component part. -/
private def ExternalInsertionDiagram.unflattenedLegInComponent {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.componentPartition.parts) (leg : ExternalInsertionLeg E S) : Prop :=
  match leg with
  | .inl e => (Sum.inl e : ExternalInsertionVertex E S) ∈
      (B : Finset (ExternalInsertionVertex E S))
  | .inr p => (Sum.inr p.1 : ExternalInsertionVertex E S) ∈
      (B : Finset (ExternalInsertionVertex E S))

/-- Flattening preserves the component-membership predicate. -/
private theorem ExternalInsertionDiagram.legInComponent_iff_unflattened {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.componentPartition.parts) (leg : Fin (2 * (2 * S.card + E))) :
    d.legInComponent B leg ↔
      d.unflattenedLegInComponent B (externalInsertionLegEquiv E S leg) := by
  rw [d.legInComponent_iff_vertex_mem B.2 leg]
  unfold ExternalInsertionDiagram.unflattenedLegInComponent
  unfold externalInsertionVertexOfLeg
  cases externalInsertionLegEquiv E S leg <;> rfl

/-- The legs of one component, before flattening, split into its external insertions and
the four local legs of its interaction vertices. -/
private noncomputable def ExternalInsertionDiagram.componentLegDataEquiv {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.componentPartition.parts) :
    {leg : ExternalInsertionLeg E S // d.unflattenedLegInComponent B leg} ≃
      ↥(ExternalInsertionDiagram.externalPart
        (B : Finset (ExternalInsertionVertex E S))) ⊕
        (↥(interactionSector
          (B : Finset (ExternalInsertionVertex E S))) × Fin 4) where
  toFun leg := by
    rcases leg with ⟨leg, hleg⟩
    cases leg with
    | inl e =>
        exact Sum.inl ⟨e, (ExternalInsertionDiagram.mem_externalPart
          (B : Finset (ExternalInsertionVertex E S)) e).2 hleg⟩
    | inr p =>
        exact Sum.inr (⟨p.1.1,
          (mem_interactionSector_subtype
            (B : Finset (ExternalInsertionVertex E S)) p.1).2 hleg⟩, p.2)
  invFun leg := by
    cases leg with
    | inl e =>
        exact ⟨Sum.inl e.1, by
          change (Sum.inl e.1 : ExternalInsertionVertex E S) ∈
            (B : Finset (ExternalInsertionVertex E S))
          exact (ExternalInsertionDiagram.mem_externalPart
            (B : Finset (ExternalInsertionVertex E S)) e.1).1 e.2⟩
    | inr p =>
        let v : ↥S :=
          ⟨p.1.1, interactionSector_subset
            (B : Finset (ExternalInsertionVertex E S)) p.1.2⟩
        exact ⟨Sum.inr (v, p.2), by
          change (Sum.inr v : ExternalInsertionVertex E S) ∈
            (B : Finset (ExternalInsertionVertex E S))
          exact (mem_interactionSector_subtype
            (B : Finset (ExternalInsertionVertex E S)) v).1 p.1.2⟩
  left_inv leg := by
    rcases leg with ⟨leg, hleg⟩
    cases leg with
    | inl e =>
        apply Subtype.ext
        rfl
    | inr p =>
        rcases p with ⟨v, l⟩
        apply Subtype.ext
        rfl
  right_inv leg := by
    cases leg with
    | inl e =>
        apply congrArg Sum.inl
        exact Subtype.ext (by rfl)
    | inr p =>
        rcases p with ⟨v, l⟩
        apply congrArg Sum.inr
        apply Prod.ext
        · exact Subtype.ext (by rfl)
        · rfl

/-- Reindex the flattened legs of one component by its external and interaction data. -/
private noncomputable def ExternalInsertionDiagram.componentBlockLegDataEquiv
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.componentPartition.parts) :
    {leg : Fin (2 * (2 * S.card + E)) //
      d.legInComponent (B : Finset (ExternalInsertionVertex E S)) leg} ≃
      ↥(ExternalInsertionDiagram.externalPart
        (B : Finset (ExternalInsertionVertex E S))) ⊕
        (↥(interactionSector
          (B : Finset (ExternalInsertionVertex E S))) × Fin 4) :=
  ((externalInsertionLegEquiv E S).subtypeEquiv fun leg =>
      d.legInComponent_iff_unflattened B leg).trans
    (d.componentLegDataEquiv B)

/-- Component-leg membership is invariant under the pairing partner permutation. -/
theorem ExternalInsertionDiagram.legInComponent_partner_iff {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : Finset (ExternalInsertionVertex E S))
    (leg : Fin (2 * (2 * S.card + E))) :
    d.legInComponent B leg ↔ d.legInComponent B (d.pairing.partner leg) := by
  unfold ExternalInsertionDiagram.legInComponent
  have hEq :
      d.componentBlock (externalInsertionVertexOfLeg leg) =
        d.componentBlock (externalInsertionVertexOfLeg (d.pairing.partner leg)) := by
    change d.vertexGraph.componentBlock (externalInsertionVertexOfLeg leg) =
      d.vertexGraph.componentBlock (externalInsertionVertexOfLeg (d.pairing.partner leg))
    exact d.vertexGraph.componentBlock_eq_of_reachable
      (d.pairing.vertexGraph_reachable_partner externalInsertionVertexOfLeg leg).symm
  rw [hEq]

/-- Every connected component contains an even number of external insertions. -/
theorem ExternalInsertionDiagram.externalPart_card_even {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.componentPartition.parts) :
    Even (ExternalInsertionDiagram.externalPart
      (B : Finset (ExternalInsertionVertex E S))).card := by
  classical
  let blockEquiv := d.componentBlockLegDataEquiv B
  have hcard :
      Fintype.card {leg : Fin (2 * (2 * S.card + E)) //
        d.legInComponent (B : Finset (ExternalInsertionVertex E S)) leg} =
        (ExternalInsertionDiagram.externalPart
          (B : Finset (ExternalInsertionVertex E S))).card +
          4 * (interactionSector
            (B : Finset (ExternalInsertionVertex E S))).card := by
    calc
      Fintype.card {leg : Fin (2 * (2 * S.card + E)) //
          d.legInComponent (B : Finset (ExternalInsertionVertex E S)) leg} =
          Fintype.card
            (↥(ExternalInsertionDiagram.externalPart
              (B : Finset (ExternalInsertionVertex E S))) ⊕
              (↥(interactionSector
                (B : Finset (ExternalInsertionVertex E S))) × Fin 4)) :=
        Fintype.card_congr blockEquiv
      _ = (ExternalInsertionDiagram.externalPart
            (B : Finset (ExternalInsertionVertex E S))).card +
            4 * (interactionSector
              (B : Finset (ExternalInsertionVertex E S))).card := by
        rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_coe,
          Fintype.card_coe, Fintype.card_fin]
        omega
  let restricted :=
    d.pairing.restrict
      (d.legInComponent (B : Finset (ExternalInsertionVertex E S)))
      (fun leg => d.legInComponent_partner_iff
        (B : Finset (ExternalInsertionVertex E S)) leg)
  have hEven :
      Even (Fintype.card {leg : Fin (2 * (2 * S.card + E)) //
        d.legInComponent (B : Finset (ExternalInsertionVertex E S)) leg}) :=
    restricted.even_card
  rw [hcard] at hEven
  rcases hEven with ⟨k, hk⟩
  refine ⟨k - 2 * (interactionSector
    (B : Finset (ExternalInsertionVertex E S))).card, ?_⟩
  omega

/-- The local external-sector parameter: half the number of one-legged external insertions
carried by one connected component. -/
noncomputable def ExternalInsertionDiagram.externalPairCount {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.componentPartition.parts) : ℕ :=
  (ExternalInsertionDiagram.externalPart
    (B : Finset (ExternalInsertionVertex E S))).card / 2

/-- The external sector of one component has twice its local external-pair count. -/
private theorem ExternalInsertionDiagram.externalPart_card_eq_two_mul_externalPairCount
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.componentPartition.parts) :
    (ExternalInsertionDiagram.externalPart
      (B : Finset (ExternalInsertionVertex E S))).card =
      2 * d.externalPairCount B := by
  rw [ExternalInsertionDiagram.externalPairCount]
  exact (Nat.two_mul_div_two_of_even (d.externalPart_card_even B)).symm

/-- Increasing reindexing of a component's ambient external insertions by its local external slots. -/
noncomputable def ExternalInsertionDiagram.externalPartOrderIso {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.componentPartition.parts) :
    Fin (2 * d.externalPairCount B) ≃o
      ↥(ExternalInsertionDiagram.externalPart
        (B : Finset (ExternalInsertionVertex E S))) :=
  (ExternalInsertionDiagram.externalPart
    (B : Finset (ExternalInsertionVertex E S))).orderIsoOfFin
      (d.externalPart_card_eq_two_mul_externalPairCount B)

/-- The canonical order-preserving shuffle of component-local external insertions into the
ambient external-insertion order. -/
noncomputable def ExternalInsertionDiagram.componentExternalShuffle
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S) :
    FamilySlotShuffleTo
      (fun B : d.componentPartition.parts => 2 * d.externalPairCount B)
      (2 * E) where
  slotEquiv :=
    (Equiv.sigmaCongrRight fun B : d.componentPartition.parts =>
      (d.externalPartOrderIso B).toEquiv).trans <|
      ((Equiv.subtypeUnivEquiv
        (fun e : Fin (2 * E) => Finset.mem_univ e)).symm.trans <|
        d.componentPartition.equivSigmaSubfinsets
          (Finset.univ : Finset (Fin (2 * E)))
          (fun e => (Sum.inl (e : Fin (2 * E)) :
            ExternalInsertionVertex E S))
          (fun _ => Finset.mem_univ _)
          (fun B => ExternalInsertionDiagram.externalPart
            (B : Finset (ExternalInsertionVertex E S)))
          (fun _ => Finset.subset_univ _)
          (fun B e => ExternalInsertionDiagram.mem_externalPart
            (B : Finset (ExternalInsertionVertex E S)) e)).symm
  strictMono := fun B _ _ hef =>
    (d.externalPartOrderIso B).strictMono hef

@[simp]
theorem ExternalInsertionDiagram.componentExternalShuffle_slotEquiv_apply
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.componentPartition.parts)
    (e : Fin (2 * d.externalPairCount B)) :
    d.componentExternalShuffle.slotEquiv ⟨B, e⟩ =
      (d.externalPartOrderIso B e).1 := by
  rfl

/-- Reindex the flattened legs of one component as the flattened legs of its local
external-insertion diagram. -/
private noncomputable def ExternalInsertionDiagram.componentBlockLegEquiv
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.componentPartition.parts) :
    {leg : Fin (2 * (2 * S.card + E)) //
      d.legInComponent (B : Finset (ExternalInsertionVertex E S)) leg} ≃
      Fin (2 * (2 * (interactionSector
        (B : Finset (ExternalInsertionVertex E S))).card + d.externalPairCount B)) :=
  (d.componentBlockLegDataEquiv B).trans <|
    (Equiv.sumCongr (d.externalPartOrderIso B).toEquiv (Equiv.refl _)).symm.trans <|
      (externalInsertionLegEquiv (d.externalPairCount B)
        (interactionSector
          (B : Finset (ExternalInsertionVertex E S)))).symm

/-- Restrict one connected component to a standalone external-insertion diagram on its local
external and interaction sectors. -/
noncomputable def ExternalInsertionDiagram.restrictComponent {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.componentPartition.parts) :
    ExternalInsertionDiagram ExternalLabel InternalLabel (d.externalPairCount B) N
      (interactionSector
        (B : Finset (ExternalInsertionVertex E S))) where
  externalLabel e := d.externalLabel (d.externalPartOrderIso B e).1
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
    (B : d.componentPartition.parts) :
    Fin (2 * (2 * (interactionSector
      (B : Finset (ExternalInsertionVertex E S))).card + d.externalPairCount B)) →
      Fin (2 * (2 * S.card + E)) :=
  fun p => ((d.componentBlockLegEquiv B).symm p).1

/-- The restricted component pairing partner, transported back to ambient flattened-leg
coordinates, agrees with the ambient pairing partner. -/
theorem ExternalInsertionDiagram.componentDiagramLeg_restrictComponent_pairing_partner
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.componentPartition.parts)
    (p : Fin (2 * (2 * (interactionSector
      (B : Finset (ExternalInsertionVertex E S))).card + d.externalPairCount B))) :
    d.componentDiagramLeg B ((d.restrictComponent B).pairing.partner p) =
      d.pairing.partner (d.componentDiagramLeg B p) := by
  let leg := (d.componentBlockLegEquiv B).symm p
  have h := d.pairing.restrictAlongEquiv_partner
    (d.legInComponent (B : Finset (ExternalInsertionVertex E S)))
    (fun i => d.legInComponent_partner_iff
      (B : Finset (ExternalInsertionVertex E S)) i)
    (d.componentBlockLegEquiv B) leg
  have h' := congrArg
    (fun q => (((d.componentBlockLegEquiv B).symm q :
      {leg : Fin (2 * (2 * S.card + E)) //
        d.legInComponent (B : Finset (ExternalInsertionVertex E S)) leg}) :
          Fin (2 * (2 * S.card + E)))) h
  calc
    d.componentDiagramLeg B ((d.restrictComponent B).pairing.partner p) =
        (((d.pairing.restrict
          (d.legInComponent (B : Finset (ExternalInsertionVertex E S)))
          (fun i => d.legInComponent_partner_iff
            (B : Finset (ExternalInsertionVertex E S)) i)).partner leg :
          {leg : Fin (2 * (2 * S.card + E)) //
            d.legInComponent (B : Finset (ExternalInsertionVertex E S)) leg}) :
              Fin (2 * (2 * S.card + E))) := by
      simpa [ExternalInsertionDiagram.componentDiagramLeg,
        ExternalInsertionDiagram.restrictComponent, leg] using h'
    _ = d.pairing.partner (d.componentDiagramLeg B p) := by
      rw [d.pairing.restrict_partner_val
        (d.legInComponent (B : Finset (ExternalInsertionVertex E S)))
        (fun i => d.legInComponent_partner_iff
          (B : Finset (ExternalInsertionVertex E S)) i)]
      rfl


private theorem ExternalInsertionDiagram.componentDiagramLeg_external
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.componentPartition.parts) (e : Fin (2 * d.externalPairCount B)) :
    d.componentDiagramLeg B
        (externalInsertionExternalLeg (d.externalPairCount B)
          (interactionSector
            (B : Finset (ExternalInsertionVertex E S))) e) =
      externalInsertionExternalLeg E S (d.externalPartOrderIso B e).1 := by
  apply (externalInsertionLegEquiv E S).injective
  simp [ExternalInsertionDiagram.componentDiagramLeg,
    ExternalInsertionDiagram.componentBlockLegEquiv,
    ExternalInsertionDiagram.componentBlockLegDataEquiv,
    ExternalInsertionDiagram.componentLegDataEquiv,
    externalInsertionExternalLeg]

private theorem ExternalInsertionDiagram.componentDiagramLeg_interaction
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.componentPartition.parts)
    (v : ↥(interactionSector
      (B : Finset (ExternalInsertionVertex E S)))) (l : Fin 4) :
    d.componentDiagramLeg B
        (externalInsertionInteractionLeg (E := d.externalPairCount B) v l) =
      externalInsertionInteractionLeg (E := E)
        ⟨v.1, interactionSector_subset
          (B : Finset (ExternalInsertionVertex E S)) v.2⟩ l := by
  apply (externalInsertionLegEquiv E S).injective
  simp [ExternalInsertionDiagram.componentDiagramLeg,
    ExternalInsertionDiagram.componentBlockLegEquiv,
    ExternalInsertionDiagram.componentBlockLegDataEquiv,
    ExternalInsertionDiagram.componentLegDataEquiv,
    externalInsertionInteractionLeg]

/-- The component-local flattened-leg embedding preserves the canonical external-insertion leg
order. -/
private theorem ExternalInsertionDiagram.componentDiagramLeg_strictMono
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.componentPartition.parts) :
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
      externalInsertionExternalLeg (d.externalPairCount B) T e <
        externalInsertionExternalLeg (d.externalPairCount B) T f at hab
    change
      d.componentDiagramLeg B
          (externalInsertionExternalLeg (d.externalPairCount B) T e) <
        d.componentDiagramLeg B
          (externalInsertionExternalLeg (d.externalPairCount B) T f)
    rw [d.componentDiagramLeg_external B, d.componentDiagramLeg_external B]
    change
      (externalInsertionExternalLeg E S (d.externalPartOrderIso B e).1).val <
        (externalInsertionExternalLeg E S (d.externalPartOrderIso B f).1).val
    have hef : e < f := by
      change
        (externalInsertionExternalLeg (d.externalPairCount B) T e).val <
          (externalInsertionExternalLeg (d.externalPairCount B) T f).val at hab
      simpa using hab
    simpa using (d.externalPartOrderIso B).strictMono hef
  · change
      externalInsertionExternalLeg (d.externalPairCount B) T e <
        externalInsertionInteractionLeg (E := d.externalPairCount B) w k at hab
    change
      d.componentDiagramLeg B
          (externalInsertionExternalLeg (d.externalPairCount B) T e) <
        d.componentDiagramLeg B
          (externalInsertionInteractionLeg (E := d.externalPairCount B) w k)
    rw [d.componentDiagramLeg_external B, d.componentDiagramLeg_interaction B]
    change
      (externalInsertionExternalLeg E S (d.externalPartOrderIso B e).1).val <
        (externalInsertionInteractionLeg (E := E)
          ⟨w.1, interactionSector_subset
            (B : Finset (ExternalInsertionVertex E S)) w.2⟩ k).val
    simp only [externalInsertionExternalLeg_val, externalInsertionInteractionLeg_val]
    exact Nat.lt_of_lt_of_le (d.externalPartOrderIso B e).1.isLt (by omega)
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
      have hlk : l.val < k.val := by omega
      omega
    · have hrank_ne :
          ((T.orderIsoOfFin rfl).symm v).val ≠
            ((T.orderIsoOfFin rfl).symm w).val := by
        intro h
        apply hvw
        apply (T.orderIsoOfFin rfl).symm.injective
        exact Fin.ext h
      have hl : l.val < 4 := l.isLt
      have hk : k.val < 4 := k.isLt
      have hrank :
          ((T.orderIsoOfFin rfl).symm v).val <
            ((T.orderIsoOfFin rfl).symm w).val := by
        omega
      have hvwT : v < w := by
        simpa using (T.orderIsoOfFin rfl).strictMono hrank
      let vS : ↥S :=
        ⟨v.1, interactionSector_subset
          (B : Finset (ExternalInsertionVertex E S)) v.2⟩
      let wS : ↥S :=
        ⟨w.1, interactionSector_subset
          (B : Finset (ExternalInsertionVertex E S)) w.2⟩
      have hvwS : vS < wS := by
        change v.1 < w.1
        exact hvwT
      have hamb :
          ((S.orderIsoOfFin rfl).symm vS).val <
            ((S.orderIsoOfFin rfl).symm wS).val :=
        (S.orderIsoOfFin rfl).symm.strictMono hvwS
      dsimp [vS, wS] at hamb
      omega

/-- The canonical order embedding of one restricted component's flattened legs into the ambient
external-insertion leg order. -/
noncomputable def ExternalInsertionDiagram.componentDiagramLegOrderEmbedding
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.componentPartition.parts) :
    Fin (2 * (2 * (interactionSector
      (B : Finset (ExternalInsertionVertex E S))).card + d.externalPairCount B)) ↪o
      Fin (2 * (2 * S.card + E)) :=
  OrderEmbedding.ofStrictMono (d.componentDiagramLeg B)
    (d.componentDiagramLeg_strictMono B)


/-- The image of the canonical component leg embedding is exactly the ambient legs incident to that
connected component. -/
theorem ExternalInsertionDiagram.exists_componentDiagramLeg_eq_iff
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.componentPartition.parts)
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
      (fun B : d.componentPartition.parts =>
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
          let B : d.componentPartition.parts :=
            ⟨d.componentBlock (externalInsertionVertexOfLeg leg), by
              unfold ExternalInsertionDiagram.componentBlock
              exact d.componentPartition.part_mem.2 (Finset.mem_univ _)⟩
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
    (B : d.componentPartition.parts)
    (p : Fin (2 * (2 * (interactionSector
      (B : Finset (ExternalInsertionVertex E S))).card + d.externalPairCount B))) :
    d.componentLegShuffle.slotEquiv ⟨B, p⟩ = d.componentDiagramLeg B p :=
  rfl


/-- Embed normalized pairs of a restricted component into the ambient pairing using the canonical
component leg order embedding. -/
noncomputable def ExternalInsertionDiagram.componentNormalizedPairEmbedding
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.componentPartition.parts) :
    (d.restrictComponent B).pairing.NormalizedPair ↪ d.pairing.NormalizedPair :=
  (d.restrictComponent B).pairing.normalizedPairEmbedding d.pairing
    (d.componentDiagramLegOrderEmbedding B)
    (fun p => by
      simpa [ExternalInsertionDiagram.componentDiagramLegOrderEmbedding] using
        (d.componentDiagramLeg_restrictComponent_pairing_partner B p).symm)

/-- The canonical component normalized-pair embedding preserves and reflects geometric crossings. -/
theorem ExternalInsertionDiagram.componentNormalizedPairEmbedding_crosses_iff
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.componentPartition.parts)
    (p q : (d.restrictComponent B).pairing.NormalizedPair) :
    Crosses (d.componentNormalizedPairEmbedding B p).1
        (d.componentNormalizedPairEmbedding B q).1 ↔
      Crosses p.1 q.1 := by
  simpa [ExternalInsertionDiagram.componentNormalizedPairEmbedding] using
    (d.restrictComponent B).pairing.normalizedPairEmbedding_crosses_iff d.pairing
      (d.componentDiagramLegOrderEmbedding B)
      (fun i => by
        simpa [ExternalInsertionDiagram.componentDiagramLegOrderEmbedding] using
          (d.componentDiagramLeg_restrictComponent_pairing_partner B i).symm)
      p q

/-- For a vacuum part, unflattened component legs are exactly the four local legs of the extracted
interaction vertices. -/
private noncomputable def ExternalInsertionDiagram.vacuumLegDataEquiv {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.componentPartition.parts) (hVac : d.ComponentIsVacuum B) :
    {leg : ExternalInsertionLeg E S // d.unflattenedLegInComponent B leg} ≃
      ↥(interactionSector
        (B : Finset (ExternalInsertionVertex E S))) × Fin 4 where
  toFun leg := by
    rcases leg with ⟨leg, hleg⟩
    cases leg with
    | inl e => exact False.elim (hVac ⟨e, hleg⟩)
    | inr p =>
        exact (⟨p.1.1,
          (mem_interactionSector_subtype
            (B : Finset (ExternalInsertionVertex E S)) p.1).2 hleg⟩, p.2)
  invFun p :=
    let v : ↥S :=
      ⟨p.1.1, interactionSector_subset
        (B : Finset (ExternalInsertionVertex E S)) p.1.2⟩
    ⟨Sum.inr (v, p.2), by
      change (Sum.inr v : ExternalInsertionVertex E S) ∈
        (B : Finset (ExternalInsertionVertex E S))
      exact (mem_interactionSector_subtype
        (B : Finset (ExternalInsertionVertex E S)) v).1 p.1.2⟩
  left_inv leg := by
    rcases leg with ⟨leg, hleg⟩
    cases leg with
    | inl e => exact False.elim (hVac ⟨e, hleg⟩)
    | inr p =>
        rcases p with ⟨v, l⟩
        apply Subtype.ext
        rfl
  right_inv p := by
    rcases p with ⟨v, l⟩
    apply Prod.ext
    · exact Subtype.ext (by rfl)
    · rfl

/-- Reindex the legs of a vacuum component as the flattened legs of an ordinary quartic diagram. -/
noncomputable def ExternalInsertionDiagram.vacuumBlockLegEquiv {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.componentPartition.parts) (hVac : d.ComponentIsVacuum B) :
    {leg : Fin (2 * (2 * S.card + E)) // d.legInComponent B leg} ≃
      Fin (2 * (2 * (interactionSector
        (B : Finset (ExternalInsertionVertex E S))).card)) :=
  ((externalInsertionLegEquiv E S).subtypeEquiv fun leg =>
      d.legInComponent_iff_unflattened B leg).trans
    ((d.vacuumLegDataEquiv B hVac).trans
      (quarticLegEquiv (interactionSector
        (B : Finset (ExternalInsertionVertex E S)))).symm)

/-- The perfect pairing induced on a vacuum component. -/
noncomputable def ExternalInsertionDiagram.restrictedVacuumPairing {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.componentPartition.parts) (hVac : d.ComponentIsVacuum B) :
    Pairing (2 * (interactionSector
      (B : Finset (ExternalInsertionVertex E S))).card) :=
  d.pairing.restrictAlongEquiv (d.legInComponent B)
    (fun leg => d.legInComponent_partner_iff (B : Finset (ExternalInsertionVertex E S)) leg)
    (d.vacuumBlockLegEquiv B hVac)

/-- The restricted vacuum pairing agrees with the component-restricted ambient pairing
under the vacuum leg reindexing. -/
theorem ExternalInsertionDiagram.restrictedVacuumPairing_partner_vacuumBlockLegEquiv
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.componentPartition.parts) (hVac : d.ComponentIsVacuum B)
    (leg : {leg : Fin (2 * (2 * S.card + E)) // d.legInComponent B leg}) :
    (d.restrictedVacuumPairing B hVac).partner (d.vacuumBlockLegEquiv B hVac leg) =
      d.vacuumBlockLegEquiv B hVac
        ((d.pairing.restrict (d.legInComponent B)
          (fun i => d.legInComponent_partner_iff
            (B : Finset (ExternalInsertionVertex E S)) i)).partner leg) := by
  simpa only [ExternalInsertionDiagram.restrictedVacuumPairing] using
    d.pairing.restrictAlongEquiv_partner (d.legInComponent B)
      (fun i => d.legInComponent_partner_iff
        (B : Finset (ExternalInsertionVertex E S)) i)
      (d.vacuumBlockLegEquiv B hVac) leg

/-- Restrict a vacuum component of an external-insertion diagram to an ordinary quartic diagram. -/
noncomputable def ExternalInsertionDiagram.restrictVacuumComponent {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.componentPartition.parts) (hVac : d.ComponentIsVacuum B) :
    QuarticDiagram InternalLabel N
      (interactionSector
        (B : Finset (ExternalInsertionVertex E S))) where
  vertexLabel v :=
    d.vertexLabel ⟨v.1, interactionSector_subset
      (B : Finset (ExternalInsertionVertex E S)) v.2⟩
  pairing := d.restrictedVacuumPairing B hVac

end Common
end SecondQuantization
