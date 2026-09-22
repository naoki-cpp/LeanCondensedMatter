import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Components.ComponentRestriction
import LeanCondensedMatter.Combinatorics.PerfectPairing.ComponentDecomposition
import LeanCondensedMatter.Combinatorics.FamilySlotShuffle

set_option linter.style.header false

/-!
# External-insertion component-pair equivalence

The canonical leg embeddings of all connected components exhaust the ambient flattened-leg
enumeration. Since each embedding also intertwines the restricted and ambient pairing partners, the
generic perfect-pairing component decomposition identifies the dependent sum of component-local
normalized pairs with the normalized pairs of the ambient external-insertion diagram.

This layer is statistics-independent.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*} {E N : ℕ}

/-- The component-local leg embeddings, taken over every connected component, form the canonical
order-preserving family shuffle onto the full ambient flattened-leg enumeration. -/
noncomputable def ExternalInsertionDiagram.componentLegShuffle
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S) :
    FamilySlotShuffleTo
      (fun B : d.componentPartition.parts =>
        2 * (2 * (ExternalInsertionDiagram.interactionPart
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
    (p : Fin (2 * (2 * (ExternalInsertionDiagram.interactionPart
      (B : Finset (ExternalInsertionVertex E S))).card + d.externalPairCount B))) :
    d.componentLegShuffle.slotEquiv ⟨B, p⟩ = d.componentDiagramLeg B p :=
  rfl

private theorem ExternalInsertionDiagram.componentLegShuffle_partner
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.componentPartition.parts)
    (p : Fin (2 * (2 * (ExternalInsertionDiagram.interactionPart
      (B : Finset (ExternalInsertionVertex E S))).card + d.externalPairCount B))) :
    d.pairing.partner (d.componentLegShuffle.slotEquiv ⟨B, p⟩) =
      d.componentLegShuffle.slotEquiv ⟨B, (d.restrictComponent B).pairing.partner p⟩ := by
  simpa only [ExternalInsertionDiagram.componentLegShuffle_slotEquiv_apply] using
    (d.componentDiagramLeg_restrictComponent_pairing_partner B p).symm

/-- Component-local normalized pairs, over all connected components, are equivalent to the ambient
diagram's normalized pairs. -/
noncomputable def ExternalInsertionDiagram.componentPairEquiv
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S) :
    (Σ B : d.componentPartition.parts, (d.restrictComponent B).pairing.NormalizedPair) ≃
      d.pairing.NormalizedPair :=
  d.pairing.normalizedPairSigmaEquiv
    (fun B => (d.restrictComponent B).pairing)
    d.componentLegShuffle.slotEquiv
    d.componentLegShuffle_partner

@[simp]
theorem ExternalInsertionDiagram.componentPairEquiv_apply
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.componentPartition.parts)
    (pr : (d.restrictComponent B).pairing.NormalizedPair) :
    (d.componentPairEquiv ⟨B, pr⟩).1 =
      (d.componentDiagramLeg B pr.1.1, d.componentDiagramLeg B pr.1.2) := by
  simpa only [ExternalInsertionDiagram.componentPairEquiv,
    ExternalInsertionDiagram.componentLegShuffle_slotEquiv_apply] using
    (Pairing.normalizedPairSigmaEquiv_apply_of_strictMono
      d.pairing
      (fun C => (d.restrictComponent C).pairing)
      d.componentLegShuffle.slotEquiv
      d.componentLegShuffle_partner
      (fun C => by
        change StrictMono (fun p => d.componentDiagramLeg C p)
        exact (d.componentDiagramLegOrderEmbedding C).strictMono)
      B pr)

end Common
end SecondQuantization
