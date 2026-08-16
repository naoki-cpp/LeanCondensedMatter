import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.ComponentOrder
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.ComponentRestriction
import LeanCondensedMatter.Combinatorics.PerfectPairing.Embedding

set_option linter.style.header false

/-!
# Component-local quartic pairing compatibility

This module contains the statistics-independent ordered-leg embedding and pairing compatibility used
when a quartic diagram is decomposed into connected components.  A component-local ordered leg is
embedded into an assembled global vertex order, and the transported global pairing is shown to agree
with the pairing of the restricted component.

The results depend only on `Common.QuarticDiagram`; no fermionic or bosonic operator realization is
used.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {Label : Type*} {N : ℕ}

/-- Embed a component-local ordered flattened leg into the assembled global ordered-leg
enumeration. -/
noncomputable def QuarticDiagram.componentOrderedLeg {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (shuffle : d.ComponentShuffle)
    (B : d.componentPartition.parts) :
    Fin (2 * (2 * (B : Finset (Fin N)).card)) → Fin (2 * (2 * S.card)) :=
  fun p => (orderedQuarticLegEquiv S.card).symm
    (shuffle.slotEquiv ⟨B, (orderedQuarticLegEquiv (B : Finset (Fin N)).card p).1⟩,
      (orderedQuarticLegEquiv (B : Finset (Fin N)).card p).2)

@[simp]
theorem QuarticDiagram.orderedQuarticLegEquiv_componentOrderedLeg
    {S : Finset (Fin N)} (d : QuarticDiagram Label N S)
    (shuffle : d.ComponentShuffle) (B : d.componentPartition.parts)
    (p : Fin (2 * (2 * (B : Finset (Fin N)).card))) :
    orderedQuarticLegEquiv S.card (d.componentOrderedLeg shuffle B p) =
      (shuffle.slotEquiv ⟨B, (orderedQuarticLegEquiv (B : Finset (Fin N)).card p).1⟩,
        (orderedQuarticLegEquiv (B : Finset (Fin N)).card p).2) := by
  simp [QuarticDiagram.componentOrderedLeg]

/-- The component ordered-leg embedding preserves the flattened-leg order. -/
theorem QuarticDiagram.componentOrderedLeg_strictMono {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (shuffle : d.ComponentShuffle)
    (B : d.componentPartition.parts) :
    StrictMono (d.componentOrderedLeg shuffle B) := by
  intro a b hab
  let pa := orderedQuarticLegEquiv (B : Finset (Fin N)).card a
  let pb := orderedQuarticLegEquiv (B : Finset (Fin N)).card b
  have hab' :
      (orderedQuarticLegEquiv (B : Finset (Fin N)).card).symm pa <
        (orderedQuarticLegEquiv (B : Finset (Fin N)).card).symm pb := by
    simpa [pa, pb] using hab
  change (orderedQuarticLegEquiv S.card).symm
      (shuffle.slotEquiv ⟨B, pa.1⟩, pa.2) <
    (orderedQuarticLegEquiv S.card).symm
      (shuffle.slotEquiv ⟨B, pb.1⟩, pb.2)
  by_cases hslot : pa.1 = pb.1
  · have hlocal : pa.2 < pb.2 :=
      (orderedQuarticLegEquiv_symm_lt_symm_iff_snd_lt_of_fst_eq
        (B : Finset (Fin N)).card pa pb hslot).1 hab'
    have hmap : shuffle.slotEquiv ⟨B, pa.1⟩ = shuffle.slotEquiv ⟨B, pb.1⟩ := by
      rw [hslot]
    exact (orderedQuarticLegEquiv_symm_lt_symm_iff_snd_lt_of_fst_eq
      S.card
      (shuffle.slotEquiv ⟨B, pa.1⟩, pa.2)
      (shuffle.slotEquiv ⟨B, pb.1⟩, pb.2) hmap).2 hlocal
  · have hslotLt : pa.1 < pb.1 :=
      (orderedQuarticLegEquiv_symm_lt_symm_iff_fst_lt_of_ne
        (B : Finset (Fin N)).card pa.1 pb.1 pa.2 pb.2 hslot).1 hab'
    have hmapLt := shuffle.strictMono B hslotLt
    exact (orderedQuarticLegEquiv_symm_lt_symm_iff_fst_lt_of_ne
      S.card _ _ _ _ (ne_of_lt hmapLt)).2 hmapLt

/-- The canonical order embedding of one component's flattened legs into the assembled order. -/
noncomputable def QuarticDiagram.componentOrderedLegOrderEmbedding {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (shuffle : d.ComponentShuffle)
    (B : d.componentPartition.parts) :
    Fin (2 * (2 * (B : Finset (Fin N)).card)) ↪o Fin (2 * (2 * S.card)) :=
  OrderEmbedding.ofStrictMono (d.componentOrderedLeg shuffle B)
    (d.componentOrderedLeg_strictMono shuffle B)

/-- The assembled global order sends a component slot to the same underlying labelled vertex as its
component-local order. -/
theorem QuarticDiagram.assembleVertexOrder_componentSlot_val
    {S : Finset (Fin N)} (d : QuarticDiagram Label N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (B : d.componentPartition.parts) (i : Fin (B : Finset (Fin N)).card) :
    ((d.assembleVertexOrder orders shuffle (shuffle.slotEquiv ⟨B, i⟩) : ↥S) : Fin N) =
      ((orders B i : ↥(B : Finset (Fin N))) : Fin N) := by
  simp [QuarticDiagram.assembleVertexOrder,
    QuarticDiagram.componentVertexEquiv, Finpartition.equivSigmaParts]

/-- Vertex labels agree between the assembled global diagram and a restricted component. -/
theorem QuarticDiagram.restrictComponent_vertexLabel_componentOrder
    {S : Finset (Fin N)} (d : QuarticDiagram Label N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (B : d.componentPartition.parts) (i : Fin (B : Finset (Fin N)).card) :
    (d.restrictComponent B.2).vertexLabel (orders B i) =
      d.vertexLabel (d.assembleVertexOrder orders shuffle (shuffle.slotEquiv ⟨B, i⟩)) := by
  unfold QuarticDiagram.restrictComponent
  apply congrArg d.vertexLabel
  apply Subtype.ext
  simpa using (d.assembleVertexOrder_componentSlot_val orders shuffle B i).symm

@[simp]
theorem vertexOfLeg_orderedLegToDiagramLeg (S : Finset (Fin N))
    (order : QuarticVertexOrder S) (p : Fin (2 * (2 * S.card))) :
    vertexOfLeg (orderedLegToDiagramLeg S order p) =
      order (orderedQuarticLegEquiv S.card p).1 := by
  change ((quarticLegEquiv S) ((orderedLegToDiagramLeg S order) p)).1 = _
  simp [orderedLegToDiagramLeg]

@[simp]
theorem localLegOfLeg_orderedLegToDiagramLeg (S : Finset (Fin N))
    (order : QuarticVertexOrder S) (p : Fin (2 * (2 * S.card))) :
    localLegOfLeg (orderedLegToDiagramLeg S order p) =
      (orderedQuarticLegEquiv S.card p).2 := by
  change ((quarticLegEquiv S) ((orderedLegToDiagramLeg S order) p)).2 = _
  simp [orderedLegToDiagramLeg]

/-- Embed a flattened leg of a restricted component into the ambient diagram's fixed flattened-leg
enumeration. -/
noncomputable def QuarticDiagram.componentDiagramLeg {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (B : d.componentPartition.parts) :
    Fin (2 * (2 * (B : Finset (Fin N)).card)) → Fin (2 * (2 * S.card)) :=
  fun p => ((d.blockLegEquiv B.2).symm p).1

/-- `componentDiagramLeg` preserves the underlying labelled vertex. -/
theorem QuarticDiagram.vertexOfLeg_componentDiagramLeg_val
    {S : Finset (Fin N)} (d : QuarticDiagram Label N S)
    (B : d.componentPartition.parts)
    (p : Fin (2 * (2 * (B : Finset (Fin N)).card))) :
    ((vertexOfLeg (d.componentDiagramLeg B p) : ↥S) : Fin N) =
      ((vertexOfLeg p : ↥(B : Finset (Fin N))) : Fin N) := by
  let leg := (d.blockLegEquiv B.2).symm p
  have h := d.vertexOfLeg_blockLegEquiv B.2 leg
  have h' := congrArg (fun v : ↥(B : Finset (Fin N)) => (v : Fin N)) h
  simpa [QuarticDiagram.componentDiagramLeg, leg,
    QuarticDiagram.subtypeMemBlockEquiv] using h'.symm

/-- `componentDiagramLeg` preserves the local leg index. -/
theorem QuarticDiagram.localLegOfLeg_componentDiagramLeg
    {S : Finset (Fin N)} (d : QuarticDiagram Label N S)
    (B : d.componentPartition.parts)
    (p : Fin (2 * (2 * (B : Finset (Fin N)).card))) :
    localLegOfLeg (d.componentDiagramLeg B p) = localLegOfLeg p := by
  let leg := (d.blockLegEquiv B.2).symm p
  have h := d.localLegOfLeg_blockLegEquiv B.2 leg
  simpa [QuarticDiagram.componentDiagramLeg, leg] using h.symm

/-- Passing a component-local ordered leg to the ambient fixed diagram-leg coordinates agrees with
first embedding it into the assembled global ordered-leg enumeration. -/
theorem QuarticDiagram.orderedLegToDiagramLeg_componentOrderedLeg
    {S : Finset (Fin N)} (d : QuarticDiagram Label N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (B : d.componentPartition.parts)
    (p : Fin (2 * (2 * (B : Finset (Fin N)).card))) :
    orderedLegToDiagramLeg S (d.assembleVertexOrder orders shuffle)
        (d.componentOrderedLeg shuffle B p) =
      d.componentDiagramLeg B
        (orderedLegToDiagramLeg (B : Finset (Fin N)) (orders B) p) := by
  apply (quarticLegEquiv S).injective
  apply Prod.ext
  · change vertexOfLeg
      (orderedLegToDiagramLeg S (d.assembleVertexOrder orders shuffle)
        (d.componentOrderedLeg shuffle B p)) =
      vertexOfLeg
        (d.componentDiagramLeg B
          (orderedLegToDiagramLeg (B : Finset (Fin N)) (orders B) p))
    apply Subtype.ext
    simp only [vertexOfLeg_orderedLegToDiagramLeg,
      d.orderedQuarticLegEquiv_componentOrderedLeg]
    calc
      ((d.assembleVertexOrder orders shuffle
          (shuffle.slotEquiv
            ⟨B, (orderedQuarticLegEquiv (B : Finset (Fin N)).card p).1⟩) : ↥S) : Fin N) =
          ((orders B (orderedQuarticLegEquiv (B : Finset (Fin N)).card p).1 :
            ↥(B : Finset (Fin N))) : Fin N) :=
        d.assembleVertexOrder_componentSlot_val orders shuffle B _
      _ = ((vertexOfLeg
          (orderedLegToDiagramLeg (B : Finset (Fin N)) (orders B) p) :
            ↥(B : Finset (Fin N))) : Fin N) := by simp
      _ = ((vertexOfLeg
          (d.componentDiagramLeg B
            (orderedLegToDiagramLeg (B : Finset (Fin N)) (orders B) p)) : ↥S) : Fin N) :=
        (d.vertexOfLeg_componentDiagramLeg_val B _).symm
  · change localLegOfLeg
      (orderedLegToDiagramLeg S (d.assembleVertexOrder orders shuffle)
        (d.componentOrderedLeg shuffle B p)) =
      localLegOfLeg
        (d.componentDiagramLeg B
          (orderedLegToDiagramLeg (B : Finset (Fin N)) (orders B) p))
    simp [d.localLegOfLeg_componentDiagramLeg]

/-- The restricted pairing partner, transported back to ambient fixed diagram-leg coordinates,
agrees with the ambient diagram pairing partner. -/
theorem QuarticDiagram.componentDiagramLeg_restrictedPairing_partner
    {S : Finset (Fin N)} (d : QuarticDiagram Label N S)
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
      simpa [QuarticDiagram.componentDiagramLeg, leg] using h'
    _ = d.pairing.partner (d.componentDiagramLeg B p) := by
      rw [d.restrictedPartner_val (B : Finset (Fin N))]
      rfl

/-- The assembled global ordered pairing partner is the component ordered-leg embedding of the
component-local ordered pairing partner. -/
theorem QuarticDiagram.pairingInOrder_partner_componentOrderedLeg
    {S : Finset (Fin N)} (d : QuarticDiagram Label N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (B : d.componentPartition.parts)
    (p : Fin (2 * (2 * (B : Finset (Fin N)).card))) :
    (d.pairingInOrder (d.assembleVertexOrder orders shuffle)).partner
        (d.componentOrderedLeg shuffle B p) =
      d.componentOrderedLeg shuffle B
        (((d.restrictComponent B.2).pairingInOrder (orders B)).partner p) := by
  apply (orderedLegToDiagramLeg S (d.assembleVertexOrder orders shuffle)).injective
  simp only [QuarticDiagram.pairingInOrder,
    Combinatorics.Pairing.relabel_partner, Equiv.apply_symm_apply]
  rw [d.orderedLegToDiagramLeg_componentOrderedLeg orders shuffle B]
  rw [d.orderedLegToDiagramLeg_componentOrderedLeg orders shuffle B]
  rw [d.restrictComponent_pairing B.2]
  simpa only [Equiv.apply_symm_apply] using
    (d.componentDiagramLeg_restrictedPairing_partner B
      (orderedLegToDiagramLeg (B : Finset (Fin N)) (orders B) p)).symm

/-- A component-local normalized pair maps to, and is reflected by, the corresponding normalized
pair of the assembled global ordered pairing. -/
theorem QuarticDiagram.mem_pairingInOrder_pairs_componentOrderedLeg_iff
    {S : Finset (Fin N)} (d : QuarticDiagram Label N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (B : d.componentPartition.parts)
    (a b : Fin (2 * (2 * (B : Finset (Fin N)).card))) :
    (d.componentOrderedLeg shuffle B a, d.componentOrderedLeg shuffle B b) ∈
        (d.pairingInOrder (d.assembleVertexOrder orders shuffle)).pairs ↔
      (a, b) ∈ ((d.restrictComponent B.2).pairingInOrder (orders B)).pairs := by
  let e := d.componentOrderedLegOrderEmbedding shuffle B
  change (e a, e b) ∈
      (d.pairingInOrder (d.assembleVertexOrder orders shuffle)).pairs ↔
    (a, b) ∈ ((d.restrictComponent B.2).pairingInOrder (orders B)).pairs
  exact
    ((d.restrictComponent B.2).pairingInOrder (orders B)).mem_pairs_map_iff
      (d.pairingInOrder (d.assembleVertexOrder orders shuffle)) e
      (by
        intro p
        change (d.pairingInOrder (d.assembleVertexOrder orders shuffle)).partner
            (d.componentOrderedLeg shuffle B p) =
          d.componentOrderedLeg shuffle B
            (((d.restrictComponent B.2).pairingInOrder (orders B)).partner p)
        exact d.pairingInOrder_partner_componentOrderedLeg orders shuffle B p)
      a b

end Common
end SecondQuantization