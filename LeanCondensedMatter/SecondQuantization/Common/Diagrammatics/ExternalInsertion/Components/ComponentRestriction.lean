import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Components.ComponentPartition
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Core.Diagram
import LeanCondensedMatter.Combinatorics.PerfectPairing.Restriction
import LeanCondensedMatter.Combinatorics.InvolutionCard
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
predicate and the domain-specific leg reindexing.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*} {E N : ℕ}

open Classical in
/-- The interaction vertices contained in a full external-plus-interaction component part. -/
noncomputable def ExternalInsertionDiagram.interactionPart {S : Finset (Fin N)}
    (B : Finset (ExternalInsertionVertex E S)) : Finset (Fin N) :=
  S.filter fun v =>
    ∃ hv : v ∈ S, (Sum.inr ⟨v, hv⟩ : ExternalInsertionVertex E S) ∈ B

/-- Membership in the interaction part is membership of the corresponding interaction vertex in the
full component part. -/
theorem ExternalInsertionDiagram.mem_interactionPart {S : Finset (Fin N)}
    (B : Finset (ExternalInsertionVertex E S)) (v : Fin N) :
    v ∈ ExternalInsertionDiagram.interactionPart B ↔
      ∃ hv : v ∈ S, (Sum.inr ⟨v, hv⟩ : ExternalInsertionVertex E S) ∈ B := by
  classical
  unfold ExternalInsertionDiagram.interactionPart
  rw [Finset.mem_filter]
  constructor
  · exact And.right
  · intro h
    exact ⟨h.choose, h⟩

/-- Membership in the interaction part for a vertex already carrying its ambient-membership proof. -/
@[simp]
theorem ExternalInsertionDiagram.mem_interactionPart_subtype {S : Finset (Fin N)}
    (B : Finset (ExternalInsertionVertex E S)) (v : ↥S) :
    (v : Fin N) ∈ ExternalInsertionDiagram.interactionPart B ↔
      (Sum.inr v : ExternalInsertionVertex E S) ∈ B := by
  rw [ExternalInsertionDiagram.mem_interactionPart]
  constructor
  · rintro ⟨hv, h⟩
    have hvEq : (⟨(v : Fin N), hv⟩ : ↥S) = v := Subtype.ext (by rfl)
    simpa only [hvEq] using h
  · intro h
    refine ⟨v.2, ?_⟩
    have hvEq : (⟨(v : Fin N), v.2⟩ : ↥S) = v := Subtype.ext (by rfl)
    simpa only [hvEq] using h

/-- The interaction part of a full component is contained in the ambient interaction-vertex set. -/
theorem ExternalInsertionDiagram.interactionPart_subset {S : Finset (Fin N)}
    (B : Finset (ExternalInsertionVertex E S)) :
    ExternalInsertionDiagram.interactionPart B ⊆ S := by
  intro v hv
  obtain ⟨hvS, _⟩ := (ExternalInsertionDiagram.mem_interactionPart B v).1 hv
  exact hvS

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
        (↥(ExternalInsertionDiagram.interactionPart
          (B : Finset (ExternalInsertionVertex E S))) × Fin 4) where
  toFun leg := by
    rcases leg with ⟨leg, hleg⟩
    cases leg with
    | inl e =>
        exact Sum.inl ⟨e, (ExternalInsertionDiagram.mem_externalPart
          (B : Finset (ExternalInsertionVertex E S)) e).2 hleg⟩
    | inr p =>
        exact Sum.inr (⟨p.1.1,
          (ExternalInsertionDiagram.mem_interactionPart_subtype
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
          ⟨p.1.1, ExternalInsertionDiagram.interactionPart_subset
            (B : Finset (ExternalInsertionVertex E S)) p.1.2⟩
        exact ⟨Sum.inr (v, p.2), by
          change (Sum.inr v : ExternalInsertionVertex E S) ∈
            (B : Finset (ExternalInsertionVertex E S))
          exact (ExternalInsertionDiagram.mem_interactionPart_subtype
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
        (↥(ExternalInsertionDiagram.interactionPart
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
          4 * (ExternalInsertionDiagram.interactionPart
            (B : Finset (ExternalInsertionVertex E S))).card := by
    calc
      Fintype.card {leg : Fin (2 * (2 * S.card + E)) //
          d.legInComponent (B : Finset (ExternalInsertionVertex E S)) leg} =
          Fintype.card
            (↥(ExternalInsertionDiagram.externalPart
              (B : Finset (ExternalInsertionVertex E S))) ⊕
              (↥(ExternalInsertionDiagram.interactionPart
                (B : Finset (ExternalInsertionVertex E S))) × Fin 4)) :=
        Fintype.card_congr blockEquiv
      _ = (ExternalInsertionDiagram.externalPart
            (B : Finset (ExternalInsertionVertex E S))).card +
            4 * (ExternalInsertionDiagram.interactionPart
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
  refine ⟨k - 2 * (ExternalInsertionDiagram.interactionPart
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

/-- Reindex the flattened legs of one component as the flattened legs of its local
external-insertion diagram. -/
private noncomputable def ExternalInsertionDiagram.componentBlockLegEquiv
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.componentPartition.parts) :
    {leg : Fin (2 * (2 * S.card + E)) //
      d.legInComponent (B : Finset (ExternalInsertionVertex E S)) leg} ≃
      Fin (2 * (2 * (ExternalInsertionDiagram.interactionPart
        (B : Finset (ExternalInsertionVertex E S))).card + d.externalPairCount B)) :=
  (d.componentBlockLegDataEquiv B).trans <|
    (Equiv.sumCongr (d.externalPartOrderIso B).toEquiv (Equiv.refl _)).symm.trans <|
      (externalInsertionLegEquiv (d.externalPairCount B)
        (ExternalInsertionDiagram.interactionPart
          (B : Finset (ExternalInsertionVertex E S)))).symm

/-- Restrict one connected component to a standalone external-insertion diagram on its local
external and interaction sectors. -/
noncomputable def ExternalInsertionDiagram.restrictComponent {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.componentPartition.parts) :
    ExternalInsertionDiagram ExternalLabel InternalLabel (d.externalPairCount B) N
      (ExternalInsertionDiagram.interactionPart
        (B : Finset (ExternalInsertionVertex E S))) where
  externalLabel e := d.externalLabel (d.externalPartOrderIso B e).1
  vertexLabel v :=
    d.vertexLabel ⟨v.1, ExternalInsertionDiagram.interactionPart_subset
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
    Fin (2 * (2 * (ExternalInsertionDiagram.interactionPart
      (B : Finset (ExternalInsertionVertex E S))).card + d.externalPairCount B)) →
      Fin (2 * (2 * S.card + E)) :=
  fun p => ((d.componentBlockLegEquiv B).symm p).1

/-- The restricted component pairing partner, transported back to ambient flattened-leg
coordinates, agrees with the ambient pairing partner. -/
theorem ExternalInsertionDiagram.componentDiagramLeg_restrictComponent_pairing_partner
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.componentPartition.parts)
    (p : Fin (2 * (2 * (ExternalInsertionDiagram.interactionPart
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
          (ExternalInsertionDiagram.interactionPart
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
    (v : ↥(ExternalInsertionDiagram.interactionPart
      (B : Finset (ExternalInsertionVertex E S)))) (l : Fin 4) :
    d.componentDiagramLeg B
        (externalInsertionInteractionLeg (E := d.externalPairCount B) v l) =
      externalInsertionInteractionLeg (E := E)
        ⟨v.1, ExternalInsertionDiagram.interactionPart_subset
          (B : Finset (ExternalInsertionVertex E S)) v.2⟩ l := by
  apply (externalInsertionLegEquiv E S).injective
  simp [ExternalInsertionDiagram.componentDiagramLeg,
    ExternalInsertionDiagram.componentBlockLegEquiv,
    ExternalInsertionDiagram.componentBlockLegDataEquiv,
    ExternalInsertionDiagram.componentLegDataEquiv,
    externalInsertionInteractionLeg]

/-- The component-local flattened-leg embedding preserves the canonical external-insertion leg
order. -/
theorem ExternalInsertionDiagram.componentDiagramLeg_strictMono
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.componentPartition.parts) :
    StrictMono (d.componentDiagramLeg B) := by
  let T :=
    ExternalInsertionDiagram.interactionPart
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
    rw [d.componentDiagramLeg_external B, d.componentDiagramLeg_interaction B]
    change
      (externalInsertionExternalLeg E S (d.externalPartOrderIso B e).1).val <
        (externalInsertionInteractionLeg (E := E)
          ⟨w.1, ExternalInsertionDiagram.interactionPart_subset
            (B : Finset (ExternalInsertionVertex E S)) w.2⟩ k).val
    simp
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
    rw [d.componentDiagramLeg_interaction B, d.componentDiagramLeg_interaction B]
    change
      (externalInsertionInteractionLeg (E := E)
        ⟨v.1, ExternalInsertionDiagram.interactionPart_subset
          (B : Finset (ExternalInsertionVertex E S)) v.2⟩ l).val <
        (externalInsertionInteractionLeg (E := E)
          ⟨w.1, ExternalInsertionDiagram.interactionPart_subset
            (B : Finset (ExternalInsertionVertex E S)) w.2⟩ k).val
    change
      (externalInsertionInteractionLeg (E := d.externalPairCount B) v l).val <
        (externalInsertionInteractionLeg (E := d.externalPairCount B) w k).val at hab
    simp at hab ⊢
    by_cases hvw : v = w
    · subst w
      have hlk : l.val < k.val := by omega
      omega
    · have hrank :
          ((T.orderIsoOfFin rfl).symm v).val <
            ((T.orderIsoOfFin rfl).symm w).val := by
        omega
      have hvwT : v < w := (T.orderIsoOfFin rfl).strictMono hrank
      let vS : ↥S :=
        ⟨v.1, ExternalInsertionDiagram.interactionPart_subset
          (B : Finset (ExternalInsertionVertex E S)) v.2⟩
      let wS : ↥S :=
        ⟨w.1, ExternalInsertionDiagram.interactionPart_subset
          (B : Finset (ExternalInsertionVertex E S)) w.2⟩
      have hvwS : vS < wS := by
        change v.1 < w.1
        exact hvwT
      have hamb :
          ((S.orderIsoOfFin rfl).symm vS).val <
            ((S.orderIsoOfFin rfl).symm wS).val :=
        (S.orderIsoOfFin rfl).symm.strictMono hvwS
      omega

/-- The canonical order embedding of one restricted component's flattened legs into the ambient
external-insertion leg order. -/
noncomputable def ExternalInsertionDiagram.componentDiagramLegOrderEmbedding
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.componentPartition.parts) :
    Fin (2 * (2 * (ExternalInsertionDiagram.interactionPart
      (B : Finset (ExternalInsertionVertex E S))).card + d.externalPairCount B)) ↪o
      Fin (2 * (2 * S.card + E)) :=
  OrderEmbedding.ofStrictMono (d.componentDiagramLeg B)
    (d.componentDiagramLeg_strictMono B)

/-- For a vacuum part, unflattened component legs are exactly the four local legs of the extracted
interaction vertices. -/
private noncomputable def ExternalInsertionDiagram.vacuumLegDataEquiv {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.componentPartition.parts) (hVac : d.ComponentIsVacuum B) :
    {leg : ExternalInsertionLeg E S // d.unflattenedLegInComponent B leg} ≃
      ↥(ExternalInsertionDiagram.interactionPart
        (B : Finset (ExternalInsertionVertex E S))) × Fin 4 where
  toFun leg := by
    rcases leg with ⟨leg, hleg⟩
    cases leg with
    | inl e => exact False.elim (hVac ⟨e, hleg⟩)
    | inr p =>
        exact (⟨p.1.1,
          (ExternalInsertionDiagram.mem_interactionPart_subtype
            (B : Finset (ExternalInsertionVertex E S)) p.1).2 hleg⟩, p.2)
  invFun p :=
    let v : ↥S :=
      ⟨p.1.1, ExternalInsertionDiagram.interactionPart_subset
        (B : Finset (ExternalInsertionVertex E S)) p.1.2⟩
    ⟨Sum.inr (v, p.2), by
      change (Sum.inr v : ExternalInsertionVertex E S) ∈
        (B : Finset (ExternalInsertionVertex E S))
      exact (ExternalInsertionDiagram.mem_interactionPart_subtype
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
      Fin (2 * (2 * (ExternalInsertionDiagram.interactionPart
        (B : Finset (ExternalInsertionVertex E S))).card)) :=
  ((externalInsertionLegEquiv E S).subtypeEquiv fun leg =>
      d.legInComponent_iff_unflattened B leg).trans
    ((d.vacuumLegDataEquiv B hVac).trans
      (quarticLegEquiv (ExternalInsertionDiagram.interactionPart
        (B : Finset (ExternalInsertionVertex E S)))).symm)

/-- The perfect pairing induced on a vacuum component. -/
noncomputable def ExternalInsertionDiagram.restrictedVacuumPairing {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.componentPartition.parts) (hVac : d.ComponentIsVacuum B) :
    Pairing (2 * (ExternalInsertionDiagram.interactionPart
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
      (ExternalInsertionDiagram.interactionPart
        (B : Finset (ExternalInsertionVertex E S))) where
  vertexLabel v :=
    d.vertexLabel ⟨v.1, ExternalInsertionDiagram.interactionPart_subset
      (B : Finset (ExternalInsertionVertex E S)) v.2⟩
  pairing := d.restrictedVacuumPairing B hVac

end Common
end SecondQuantization
