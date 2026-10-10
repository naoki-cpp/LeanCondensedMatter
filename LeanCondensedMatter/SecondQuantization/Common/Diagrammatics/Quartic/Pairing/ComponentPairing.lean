import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Components.ComponentOrder
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Components.ComponentRestriction

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

/-- The normalized ordered pairs of one restricted component. -/
abbrev QuarticDiagram.LocalOrderedPair {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (orders : d.ComponentVertexOrders)
    (B : d.vertexGraph.componentPartitionOn.parts) :=
  ((d.restrictComponent B.2).pairingInOrder (orders B)).NormalizedPair

/-- Embed a component-local ordered flattened leg into the assembled global ordered-leg
enumeration. -/
noncomputable def QuarticDiagram.componentOrderedLeg {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (shuffle : d.ComponentShuffle)
    (B : d.vertexGraph.componentPartitionOn.parts) :
    Fin (2 * (2 * (B : Finset (Fin N)).card)) → Fin (2 * (2 * S.card)) :=
  fun p => (orderedQuarticLegEquiv S.card).symm
    (shuffle.slotEquiv ⟨B, (orderedQuarticLegEquiv (B : Finset (Fin N)).card p).1⟩,
      (orderedQuarticLegEquiv (B : Finset (Fin N)).card p).2)

@[simp]
theorem QuarticDiagram.orderedQuarticLegEquiv_componentOrderedLeg
    {S : Finset (Fin N)} (d : QuarticDiagram Label N S)
    (shuffle : d.ComponentShuffle) (B : d.vertexGraph.componentPartitionOn.parts)
    (p : Fin (2 * (2 * (B : Finset (Fin N)).card))) :
    orderedQuarticLegEquiv S.card (d.componentOrderedLeg shuffle B p) =
      (shuffle.slotEquiv ⟨B, (orderedQuarticLegEquiv (B : Finset (Fin N)).card p).1⟩,
        (orderedQuarticLegEquiv (B : Finset (Fin N)).card p).2) := by
  simp [QuarticDiagram.componentOrderedLeg]

/-- The component ordered-leg embedding preserves the flattened-leg order. -/
theorem QuarticDiagram.componentOrderedLeg_strictMono {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (shuffle : d.ComponentShuffle)
    (B : d.vertexGraph.componentPartitionOn.parts) :
    StrictMono (d.componentOrderedLeg shuffle B) := by
  intro a b hab
  have hab' :=
    (FiniteIndex.blockEquiv_lt_iff
      (by ring : 2 * (2 * (B : Finset (Fin N)).card) =
        (B : Finset (Fin N)).card * 4) a b).mp hab
  apply (FiniteIndex.blockEquiv_lt_iff
    (by ring : 2 * (2 * S.card) = S.card * 4)
    (d.componentOrderedLeg shuffle B a) (d.componentOrderedLeg shuffle B b)).2
  change
    (orderedQuarticLegEquiv S.card (d.componentOrderedLeg shuffle B a)).1 <
        (orderedQuarticLegEquiv S.card (d.componentOrderedLeg shuffle B b)).1 ∨
      ((orderedQuarticLegEquiv S.card (d.componentOrderedLeg shuffle B a)).1 =
          (orderedQuarticLegEquiv S.card (d.componentOrderedLeg shuffle B b)).1 ∧
        (orderedQuarticLegEquiv S.card (d.componentOrderedLeg shuffle B a)).2 <
          (orderedQuarticLegEquiv S.card (d.componentOrderedLeg shuffle B b)).2)
  simp only [d.orderedQuarticLegEquiv_componentOrderedLeg]
  rcases hab' with hslot | ⟨hslot, hlocal⟩
  · exact Or.inl (shuffle.strictMono B hslot)
  · exact Or.inr ⟨congrArg (fun i => shuffle.slotEquiv ⟨B, i⟩) hslot, hlocal⟩

/-- The assembled global order sends a component slot to the same underlying labelled vertex as its
component-local order. -/
theorem QuarticDiagram.assembleVertexOrder_componentSlot_val
    {S : Finset (Fin N)} (d : QuarticDiagram Label N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (B : d.vertexGraph.componentPartitionOn.parts) (i : Fin (B : Finset (Fin N)).card) :
    ((d.assembleVertexOrder orders shuffle (shuffle.slotEquiv ⟨B, i⟩) : ↥S) : Fin N) =
      ((orders B i : ↥(B : Finset (Fin N))) : Fin N) := by
  let π := d.vertexGraph.componentPartitionOn
  have hslot :
      (π.assembleOrder orders shuffle).symm (π.partEquiv orders ⟨B, i⟩) =
        shuffle.slotEquiv ⟨B, i⟩ := by
    simpa [Finpartition.assembleOrder, Finpartition.partEquiv] using
      (Combinatorics.assembleFamilyOrderOfSize_symm_apply
        (F := fun C : π.parts => ↥(C : Finset (Fin N)))
        (size := fun C : π.parts => (C : Finset (Fin N)).card)
        π.equivSigmaParts orders shuffle B i)
  have hvertex :
      π.assembleOrder orders shuffle (shuffle.slotEquiv ⟨B, i⟩) =
        π.partEquiv orders ⟨B, i⟩ := by
    apply (π.assembleOrder orders shuffle).symm.injective
    simpa using hslot.symm
  change ((π.assembleOrder orders shuffle (shuffle.slotEquiv ⟨B, i⟩) : ↥S) : Fin N) = _
  rw [hvertex]
  simp [Finpartition.partEquiv, Finpartition.equivSigmaParts]

/-- Vertex labels agree between the assembled global diagram and a restricted component. -/
theorem QuarticDiagram.restrictComponent_vertexLabel_componentOrder
    {S : Finset (Fin N)} (d : QuarticDiagram Label N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (B : d.vertexGraph.componentPartitionOn.parts) (i : Fin (B : Finset (Fin N)).card) :
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
    (d : QuarticDiagram Label N S) (B : d.vertexGraph.componentPartitionOn.parts) :
    Fin (2 * (2 * (B : Finset (Fin N)).card)) → Fin (2 * (2 * S.card)) :=
  fun p => ((d.blockLegEquiv B.2).symm p).1

/-- `componentDiagramLeg` preserves the underlying labelled vertex. -/
theorem QuarticDiagram.vertexOfLeg_componentDiagramLeg_val
    {S : Finset (Fin N)} (d : QuarticDiagram Label N S)
    (B : d.vertexGraph.componentPartitionOn.parts)
    (p : Fin (2 * (2 * (B : Finset (Fin N)).card))) :
    ((vertexOfLeg (d.componentDiagramLeg B p) : ↥S) : Fin N) =
      ((vertexOfLeg p : ↥(B : Finset (Fin N))) : Fin N) := by
  let leg := (d.blockLegEquiv B.2).symm p
  have h := d.vertexOfLeg_blockLegEquiv B.2 leg
  have h' := congrArg (fun v : ↥(B : Finset (Fin N)) => (v : Fin N)) h
  simpa [QuarticDiagram.componentDiagramLeg, leg,
    Equiv.subtypeSubtypeEquivSubtype] using h'.symm

/-- `componentDiagramLeg` preserves the local leg index. -/
theorem QuarticDiagram.localLegOfLeg_componentDiagramLeg
    {S : Finset (Fin N)} (d : QuarticDiagram Label N S)
    (B : d.vertexGraph.componentPartitionOn.parts)
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
    (B : d.vertexGraph.componentPartitionOn.parts)
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
private theorem QuarticDiagram.componentDiagramLeg_restrictedPairing_partner
    {S : Finset (Fin N)} (d : QuarticDiagram Label N S)
    (B : d.vertexGraph.componentPartitionOn.parts)
    (p : Fin (2 * (2 * (B : Finset (Fin N)).card))) :
    d.componentDiagramLeg B ((d.restrictedPairing B.2).partner p) =
      d.pairing.partner (d.componentDiagramLeg B p) := by
  simpa [QuarticDiagram.componentDiagramLeg, QuarticDiagram.restrictedPairing] using
    d.pairing.restrictAlongEquiv_partner_symm_val
      (d.legInBlock (B : Finset (Fin N)))
      (fun i => d.legInBlock_partner_iff i) (d.blockLegEquiv B.2) p

/-- The assembled global ordered pairing partner is the component ordered-leg embedding of the
component-local ordered pairing partner. -/
theorem QuarticDiagram.pairingInOrder_partner_componentOrderedLeg
    {S : Finset (Fin N)} (d : QuarticDiagram Label N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (B : d.vertexGraph.componentPartitionOn.parts)
    (p : Fin (2 * (2 * (B : Finset (Fin N)).card))) :
    (d.pairingInOrder (d.assembleVertexOrder orders shuffle)).partner
        (d.componentOrderedLeg shuffle B p) =
      d.componentOrderedLeg shuffle B
        (((d.restrictComponent B.2).pairingInOrder (orders B)).partner p) := by
  apply (orderedLegToDiagramLeg S (d.assembleVertexOrder orders shuffle)).injective
  simp only [QuarticDiagram.pairingInOrder,
    Combinatorics.PairingOn.transport_partner, Equiv.apply_symm_apply]
  rw [d.orderedLegToDiagramLeg_componentOrderedLeg orders shuffle B]
  rw [d.orderedLegToDiagramLeg_componentOrderedLeg orders shuffle B]
  change d.pairing.partner
      (d.componentDiagramLeg B (orderedLegToDiagramLeg (B : Finset (Fin N)) (orders B) p)) =
    d.componentDiagramLeg B
      (orderedLegToDiagramLeg (B : Finset (Fin N)) (orders B)
        ((orderedLegToDiagramLeg (B : Finset (Fin N)) (orders B)).symm
          ((d.restrictedPairing B.2).partner
            (orderedLegToDiagramLeg (B : Finset (Fin N)) (orders B) p))))
  simpa only [Equiv.apply_symm_apply] using
    (d.componentDiagramLeg_restrictedPairing_partner B
      (orderedLegToDiagramLeg (B : Finset (Fin N)) (orders B) p)).symm


end Common
end SecondQuantization
