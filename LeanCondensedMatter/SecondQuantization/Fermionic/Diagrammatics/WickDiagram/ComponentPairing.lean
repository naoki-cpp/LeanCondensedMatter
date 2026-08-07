import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ComponentPairing
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.ComponentPairValue

set_option linter.style.header false

/-!
# Component-local ordered pairing compatibility

This module relates the pairing transported to an assembled global vertex order to the pairings
transported to each component-local order. It first compares both ordered-leg enumerations through
the diagram's fixed flattened-leg coordinates, then proves that the component ordered-leg embedding
intertwines the corresponding partner permutations.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics

variable {Mode : Type*} {N : ℕ}

theorem vertexOfLeg_orderedLegToDiagramLeg (S : Finset (Fin N))
    (order : Common.QuarticVertexOrder S) (p : Fin (2 * (2 * S.card))) :
    Common.vertexOfLeg (Common.orderedLegToDiagramLeg S order p) =
      order (Common.orderedQuarticLegEquiv S.card p).1 :=
  Common.vertexOfLeg_orderedLegToDiagramLeg S order p

theorem localLegOfLeg_orderedLegToDiagramLeg (S : Finset (Fin N))
    (order : Common.QuarticVertexOrder S) (p : Fin (2 * (2 * S.card))) :
    Common.localLegOfLeg (Common.orderedLegToDiagramLeg S order p) =
      (Common.orderedQuarticLegEquiv S.card p).2 :=
  Common.localLegOfLeg_orderedLegToDiagramLeg S order p

/-- Embed a flattened leg of a restricted component into the ambient diagram's fixed flattened-leg
enumeration. -/
noncomputable def QuarticWickDiagram.componentDiagramLeg {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (B : d.componentPartition.parts) :
    Fin (2 * (2 * (B : Finset (Fin N)).card)) → Fin (2 * (2 * S.card)) :=
  fun p => ((d.blockLegEquiv B.2).symm p).1

/-- `componentDiagramLeg` preserves the underlying labelled vertex. -/
theorem QuarticWickDiagram.vertexOfLeg_componentDiagramLeg_val
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (B : d.componentPartition.parts)
    (p : Fin (2 * (2 * (B : Finset (Fin N)).card))) :
    ((Common.vertexOfLeg (d.componentDiagramLeg B p) : ↥S) : Fin N) =
      ((Common.vertexOfLeg p : ↥(B : Finset (Fin N))) : Fin N) := by
  let leg := (d.blockLegEquiv B.2).symm p
  have h := d.vertexOfLeg_blockLegEquiv B.2 leg
  have h' := congrArg (fun v : ↥(B : Finset (Fin N)) => (v : Fin N)) h
  simpa [QuarticWickDiagram.componentDiagramLeg, leg,
    Common.QuarticDiagram.subtypeMemBlockEquiv] using h'.symm

/-- `componentDiagramLeg` preserves the local leg index. -/
theorem QuarticWickDiagram.localLegOfLeg_componentDiagramLeg
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (B : d.componentPartition.parts)
    (p : Fin (2 * (2 * (B : Finset (Fin N)).card))) :
    Common.localLegOfLeg (d.componentDiagramLeg B p) = Common.localLegOfLeg p := by
  let leg := (d.blockLegEquiv B.2).symm p
  have h := d.localLegOfLeg_blockLegEquiv B.2 leg
  simpa [QuarticWickDiagram.componentDiagramLeg, leg] using h.symm

/-- Passing a component-local ordered leg to the ambient fixed diagram-leg coordinates agrees with
first embedding it into the assembled global ordered-leg enumeration. -/
theorem QuarticWickDiagram.orderedLegToDiagramLeg_componentOrderedLeg
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (B : d.componentPartition.parts)
    (p : Fin (2 * (2 * (B : Finset (Fin N)).card))) :
    Common.orderedLegToDiagramLeg S (d.assembleVertexOrder orders shuffle)
        (d.componentOrderedLeg shuffle B p) =
      d.componentDiagramLeg B
        (Common.orderedLegToDiagramLeg (B : Finset (Fin N)) (orders B) p) := by
  apply (Common.quarticLegEquiv S).injective
  apply Prod.ext
  · change Common.vertexOfLeg
      (Common.orderedLegToDiagramLeg S (d.assembleVertexOrder orders shuffle)
        (d.componentOrderedLeg shuffle B p)) =
      Common.vertexOfLeg
        (d.componentDiagramLeg B
          (Common.orderedLegToDiagramLeg (B : Finset (Fin N)) (orders B) p))
    apply Subtype.ext
    simp only [Common.vertexOfLeg_orderedLegToDiagramLeg,
      d.orderedQuarticLegEquiv_componentOrderedLeg]
    calc
      ((d.assembleVertexOrder orders shuffle
          (shuffle.slotEquiv
            ⟨B, (Common.orderedQuarticLegEquiv (B : Finset (Fin N)).card p).1⟩) : ↥S) : Fin N) =
          ((orders B (Common.orderedQuarticLegEquiv (B : Finset (Fin N)).card p).1 :
            ↥(B : Finset (Fin N))) : Fin N) :=
        d.assembleVertexOrder_componentSlot_val orders shuffle B _
      _ = ((Common.vertexOfLeg
          (Common.orderedLegToDiagramLeg (B : Finset (Fin N)) (orders B) p) :
            ↥(B : Finset (Fin N))) : Fin N) := by
        simp only [Common.vertexOfLeg_orderedLegToDiagramLeg]
      _ = ((Common.vertexOfLeg
          (d.componentDiagramLeg B
            (Common.orderedLegToDiagramLeg (B : Finset (Fin N)) (orders B) p)) : ↥S) : Fin N) :=
        (d.vertexOfLeg_componentDiagramLeg_val B _).symm
  · change Common.localLegOfLeg
      (Common.orderedLegToDiagramLeg S (d.assembleVertexOrder orders shuffle)
        (d.componentOrderedLeg shuffle B p)) =
      Common.localLegOfLeg
        (d.componentDiagramLeg B
          (Common.orderedLegToDiagramLeg (B : Finset (Fin N)) (orders B) p))
    rw [Common.localLegOfLeg_orderedLegToDiagramLeg]
    rw [d.orderedQuarticLegEquiv_componentOrderedLeg]
    rw [d.localLegOfLeg_componentDiagramLeg]
    rw [Common.localLegOfLeg_orderedLegToDiagramLeg]

/-- The restricted pairing partner, transported back to ambient fixed diagram-leg coordinates,
agrees with the ambient diagram pairing partner. -/
theorem QuarticWickDiagram.componentDiagramLeg_restrictedPairing_partner
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (B : d.componentPartition.parts)
    (p : Fin (2 * (2 * (B : Finset (Fin N)).card))) :
    d.componentDiagramLeg B ((d.restrictedPairing B.2).partner p) =
      d.pairing.partner (d.componentDiagramLeg B p) := by
  let leg := (d.blockLegEquiv B.2).symm p
  have h := d.restrictedPairing_partner_blockLegEquiv B.2 leg
  have h' := congrArg
    (fun q => (((d.blockLegEquiv B.2).symm q :
      {leg : Fin (2 * (2 * S.card)) // d.legInBlock (B : Finset (Fin N)) leg}) :
        Fin (2 * (2 * S.card)))) h
  calc
    d.componentDiagramLeg B ((d.restrictedPairing B.2).partner p) =
        ((d.restrictedPartner (B : Finset (Fin N)) leg :
          {leg : Fin (2 * (2 * S.card)) // d.legInBlock (B : Finset (Fin N)) leg}) :
            Fin (2 * (2 * S.card))) := by
      simpa [QuarticWickDiagram.componentDiagramLeg, leg] using h'
    _ = d.pairing.partner (d.componentDiagramLeg B p) := by
      rw [d.restrictedPartner_val (B : Finset (Fin N))]
      rfl

/-- The assembled global ordered pairing partner is the component ordered-leg embedding of the
component-local ordered pairing partner. -/
theorem QuarticWickDiagram.pairingInOrder_partner_componentOrderedLeg
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (B : d.componentPartition.parts)
    (p : Fin (2 * (2 * (B : Finset (Fin N)).card))) :
    (d.pairingInOrder (d.assembleVertexOrder orders shuffle)).partner
        (d.componentOrderedLeg shuffle B p) =
      d.componentOrderedLeg shuffle B
        (((d.restrictComponent B.2).pairingInOrder (orders B)).partner p) := by
  apply (Common.orderedLegToDiagramLeg S (d.assembleVertexOrder orders shuffle)).injective
  simp only [Common.QuarticDiagram.pairingInOrder,
    Combinatorics.Pairing.relabel_partner, Equiv.apply_symm_apply]
  rw [d.orderedLegToDiagramLeg_componentOrderedLeg orders shuffle B]
  rw [d.orderedLegToDiagramLeg_componentOrderedLeg orders shuffle B]
  rw [d.restrictComponent_pairing B.2]
  simpa only [Equiv.apply_symm_apply] using
    (d.componentDiagramLeg_restrictedPairing_partner B
      (Common.orderedLegToDiagramLeg (B : Finset (Fin N)) (orders B) p)).symm

/-- A component-local normalized pair maps to, and is reflected by, the corresponding normalized
pair of the assembled global ordered pairing. -/
theorem QuarticWickDiagram.mem_pairingInOrder_pairs_componentOrderedLeg_iff
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (B : d.componentPartition.parts)
    (a b : Fin (2 * (2 * (B : Finset (Fin N)).card))) :
    (d.componentOrderedLeg shuffle B a, d.componentOrderedLeg shuffle B b) ∈
        (d.pairingInOrder (d.assembleVertexOrder orders shuffle)).pairs ↔
      (a, b) ∈ ((d.restrictComponent B.2).pairingInOrder (orders B)).pairs := by
  rw [Combinatorics.Pairing.mem_pairs_iff,
    Combinatorics.Pairing.mem_pairs_iff]
  let e := d.componentOrderedLegOrderEmbedding shuffle B
  constructor
  · rintro ⟨hab, hpartner⟩
    refine ⟨e.lt_iff_lt.mp hab, ?_⟩
    apply e.injective
    calc
      d.componentOrderedLeg shuffle B
          (((d.restrictComponent B.2).pairingInOrder (orders B)).partner a) =
        (d.pairingInOrder (d.assembleVertexOrder orders shuffle)).partner
          (d.componentOrderedLeg shuffle B a) :=
        (d.pairingInOrder_partner_componentOrderedLeg orders shuffle B a).symm
      _ = d.componentOrderedLeg shuffle B b := hpartner
  · rintro ⟨hab, hpartner⟩
    refine ⟨e.lt_iff_lt.mpr hab, ?_⟩
    rw [d.pairingInOrder_partner_componentOrderedLeg orders shuffle B, hpartner]

end Fermionic
end SecondQuantization
