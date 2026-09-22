import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Components.ComponentRestriction
import LeanCondensedMatter.Combinatorics.PerfectPairing.ComponentDecomposition

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

private theorem ExternalInsertionDiagram.componentLegShuffle_partner
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.vertexGraph.componentPartition.parts)
    (p : Fin (2 * (2 * (interactionSector
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
    (Σ B : d.vertexGraph.componentPartition.parts, (d.restrictComponent B).pairing.NormalizedPair) ≃
      d.pairing.NormalizedPair :=
  d.pairing.normalizedPairSigmaEquiv
    (fun B => (d.restrictComponent B).pairing)
    d.componentLegShuffle.slotEquiv
    d.componentLegShuffle_partner

@[simp]
theorem ExternalInsertionDiagram.componentPairEquiv_apply
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.vertexGraph.componentPartition.parts)
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
