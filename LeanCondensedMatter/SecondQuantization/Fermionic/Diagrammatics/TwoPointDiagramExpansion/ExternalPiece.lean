import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedLegSlotEmbedding
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedPositionLeg
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ComponentDecomposition
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.SlotCongr
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ComponentOrderedSimplex
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ComponentVertexProduct
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ExternalRestriction

set_option linter.style.header false

/-!
# The external component as a standalone two-point diagram

Restricting a fixed-external two-point diagram to its external component leaves the interaction
vertices indexed by the ambient slots that component happens to own. The linked-cluster
factorization needs the same data as a diagram in its own right, on as many slots as the component
owns, since that is the shape a perturbative coefficient is summed over.

This module performs that reindexing on the Common-owned slot set
`TwoPointDiagram.externalInteractionPart`. The slots are enumerated **in increasing order**, by
`Finset.orderIsoOfFin`, which is what makes the piece's mixed event and leg orders agree with the
ambient ones; see `MixedEventSlotEmbedding` and `MixedLegSlotEmbedding` for that comparison. The
piece keeps the ambient external labels, so it is again a fixed-external diagram for the same two
modes.

The last results identify the piece's legs with the ambient component's legs — the identification
being the very leg reindexing those order comparisons are stated for — and show that the piece pairs
exactly the legs the ambient diagram pairs, both as flattened positions and as the leg identities
`atomicLegPartner` pairs, the latter carrying no reference to the times.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode] {n : ℕ} {i j : Mode}

omit [LinearOrder Mode] [Fintype Mode] in
/-- The external component owns as many slots as the ordered-simplex integral for that component
integrates over. -/
theorem FixedExternalTwoPointWickDiagram.externalInteractionPart_card
    (d : FixedExternalTwoPointWickDiagram Mode n i j) :
    d.1.externalInteractionPart.card = d.1.interactionComponentSize d.1.externalComponentPart := rfl

/-- The increasing enumeration of the slots owned by the external component, as a relabeling onto
the standard slot set of that size. -/
noncomputable def FixedExternalTwoPointWickDiagram.externalSlotEquiv
    (d : FixedExternalTwoPointWickDiagram Mode n i j) :
    ↥d.1.externalInteractionPart ≃
      ↥(Finset.univ : Finset (Fin d.1.externalInteractionPart.card)) :=
  (d.1.externalInteractionPart.orderIsoOfFin rfl).toEquiv.symm.trans
    (Equiv.subtypeUnivEquiv
      (fun x : Fin d.1.externalInteractionPart.card => Finset.mem_univ x)).symm

omit [LinearOrder Mode] [Fintype Mode] in
@[simp]
theorem FixedExternalTwoPointWickDiagram.externalSlotEquiv_symm_coe
    (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (v : ↥(Finset.univ : Finset (Fin d.1.externalInteractionPart.card))) :
    ((d.externalSlotEquiv.symm v : ↥d.1.externalInteractionPart) : Fin n) =
      d.1.externalInteractionPart.orderEmbOfFin rfl
        (v : Fin d.1.externalInteractionPart.card) := by
  simp [FixedExternalTwoPointWickDiagram.externalSlotEquiv,
    Finset.coe_orderIsoOfFin_apply]

/-- **The external component as a standalone fixed-external two-point diagram**, on its own
interaction slots enumerated in increasing order. -/
noncomputable def FixedExternalTwoPointWickDiagram.externalPiece
    (d : FixedExternalTwoPointWickDiagram Mode n i j) :
    FixedExternalTwoPointWickDiagram Mode d.1.externalInteractionPart.card i j :=
  ⟨d.1.restrictExternalComponent.slotCongr d.externalSlotEquiv, by
    rw [Common.TwoPointDiagram.slotCongr_externalLabel]
    exact d.2⟩

omit [LinearOrder Mode] [Fintype Mode] in
/-- The piece carries the ambient external labels. -/
@[simp]
theorem FixedExternalTwoPointWickDiagram.externalPiece_externalLabel
    (d : FixedExternalTwoPointWickDiagram Mode n i j) :
    d.externalPiece.1.externalLabel = d.1.externalLabel := rfl

omit [LinearOrder Mode] [Fintype Mode] in
/-- **The piece's slot labels are the ambient labels read off in increasing slot order.** -/
@[simp]
theorem FixedExternalTwoPointWickDiagram.externalPiece_vertexLabelSequence
    (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (v : Fin d.1.externalInteractionPart.card) :
    d.externalPiece.vertexLabelSequence v =
      d.1.vertexLabel
        ⟨d.1.externalInteractionPart.orderEmbOfFin rfl v, Finset.mem_univ _⟩ := by
  unfold FixedExternalTwoPointWickDiagram.vertexLabelSequence
    FixedExternalTwoPointWickDiagram.externalPiece
  rw [Common.TwoPointDiagram.slotCongr_vertexLabel]
  unfold Common.TwoPointDiagram.restrictExternalComponent
  exact congrArg d.1.vertexLabel
    (Subtype.ext (d.externalSlotEquiv_symm_coe ⟨v, Finset.mem_univ v⟩))

omit [LinearOrder Mode] [Fintype Mode] in
/-- **The piece's legs are the ambient component's legs.** Reading a leg of the piece back through
the slot relabeling and the external-component leg reindexing recovers the ambient leg, and the
correspondence is exactly the monotone leg reindexing whose mixed order the ambient one restricts
to. -/
theorem FixedExternalTwoPointWickDiagram.externalLegDataEquiv_symm_twoPointLegDataCongr
    (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (leg : OrderedTwoPointLeg d.1.externalInteractionPart.card) :
    (d.1.externalLegDataEquiv.symm
        (Common.twoPointLegDataCongr d.externalSlotEquiv.symm leg) :
      OrderedTwoPointLeg n) =
      orderedTwoPointLegMap (d.1.externalInteractionPart.orderEmbOfFin rfl) leg := by
  cases leg with
  | inl e => rfl
  | inr p =>
      obtain ⟨w, l⟩ := p
      apply congrArg Sum.inr
      apply Prod.ext
      · exact Subtype.ext (d.externalSlotEquiv_symm_coe w)
      · rfl

/-- The flattened legs of the piece are the flattened ambient legs lying in the external
component. -/
noncomputable def FixedExternalTwoPointWickDiagram.externalPieceLegEquiv
    (d : FixedExternalTwoPointWickDiagram Mode n i j) :
    {leg : Fin (2 * (2 * (Finset.univ : Finset (Fin n)).card + 1)) //
        d.1.legInComponent (d.1.externalComponent 0) leg} ≃
      Fin (2 * (2 *
        (Finset.univ : Finset (Fin d.1.externalInteractionPart.card)).card + 1)) :=
  d.1.externalBlockLegEquiv.trans (Common.twoPointLegCongr d.externalSlotEquiv)

omit [LinearOrder Mode] [Fintype Mode] in
/-- The piece's leg reindexing is the component reindexing followed by the slot relabeling. -/
theorem FixedExternalTwoPointWickDiagram.externalPieceLegEquiv_apply
    (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (leg : {leg : Fin (2 * (2 * (Finset.univ : Finset (Fin n)).card + 1)) //
      d.1.legInComponent (d.1.externalComponent 0) leg}) :
    d.externalPieceLegEquiv leg =
      Common.twoPointLegCongr d.externalSlotEquiv (d.1.externalBlockLegEquiv leg) := rfl

omit [LinearOrder Mode] [Fintype Mode] in
/-- **The piece pairs the legs the ambient diagram pairs.** Transporting an ambient leg of the
external component to the piece and taking the piece's partner is the same as taking the ambient
partner first: the piece's pairing is the ambient one restricted. -/
theorem FixedExternalTwoPointWickDiagram.externalPiece_partner_externalPieceLegEquiv
    (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (leg : {leg : Fin (2 * (2 * (Finset.univ : Finset (Fin n)).card + 1)) //
      d.1.legInComponent (d.1.externalComponent 0) leg}) :
    d.externalPiece.1.pairing.partner (d.externalPieceLegEquiv leg) =
      d.externalPieceLegEquiv (d.1.restrictedPartner (d.1.externalComponent 0) leg) := by
  have hcongr :
      d.externalPiece.1.pairing.partner
          (Common.twoPointLegCongr d.externalSlotEquiv (d.1.externalBlockLegEquiv leg)) =
        Common.twoPointLegCongr d.externalSlotEquiv
          (d.1.restrictExternalComponent.pairing.partner (d.1.externalBlockLegEquiv leg)) :=
    Common.TwoPointDiagram.slotCongr_partner d.externalSlotEquiv
      d.1.restrictExternalComponent (d.1.externalBlockLegEquiv leg)
  simp only [FixedExternalTwoPointWickDiagram.externalPieceLegEquiv_apply]
  rw [hcongr, Common.TwoPointDiagram.restrictExternalComponent_pairing,
    Common.TwoPointDiagram.restrictedExternalPairing_partner_externalBlockLegEquiv]

omit [LinearOrder Mode] [Fintype Mode] in
/-- **A leg of the piece names the ambient leg the slot reindexing sends it to.** Reading a leg
identity of the piece back through the piece's leg reindexing and unflattening it in the ambient
diagram gives the leg `orderedTwoPointLegMap` produces. -/
theorem FixedExternalTwoPointWickDiagram.twoPointLegEquiv_externalPieceLegEquiv_symm
    (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (leg : OrderedTwoPointLeg d.1.externalInteractionPart.card) :
    Common.twoPointLegEquiv (Finset.univ : Finset (Fin n))
        ((d.externalPieceLegEquiv.symm
          ((Common.twoPointLegEquiv
            (Finset.univ : Finset (Fin d.1.externalInteractionPart.card))).symm leg)).1) =
      orderedTwoPointLegMap (d.1.externalInteractionPart.orderEmbOfFin rfl) leg := by
  have hcongr :
      Common.twoPointLegEquiv d.1.externalInteractionPart
          ((Common.twoPointLegCongr d.externalSlotEquiv).symm
            ((Common.twoPointLegEquiv
              (Finset.univ : Finset (Fin d.1.externalInteractionPart.card))).symm leg)) =
        Common.twoPointLegDataCongr d.externalSlotEquiv.symm leg := by
    rw [← Common.twoPointLegCongr_symm, Common.twoPointLegCongr_eq_trans,
      Equiv.trans_apply, Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hunfold :
      ((d.externalPieceLegEquiv.symm
          ((Common.twoPointLegEquiv
            (Finset.univ : Finset (Fin d.1.externalInteractionPart.card))).symm leg)).1 :
        Fin (2 * (2 * (Finset.univ : Finset (Fin n)).card + 1))) =
      (Common.twoPointLegEquiv (Finset.univ : Finset (Fin n))).symm
        ((d.1.externalLegDataEquiv.symm
          (Common.twoPointLegEquiv d.1.externalInteractionPart
            ((Common.twoPointLegCongr d.externalSlotEquiv).symm
              ((Common.twoPointLegEquiv
                (Finset.univ : Finset (Fin d.1.externalInteractionPart.card))).symm leg)))).1) := rfl
  rw [hunfold, hcongr, Equiv.apply_symm_apply,
    d.externalLegDataEquiv_symm_twoPointLegDataCongr]

omit [LinearOrder Mode] [Fintype Mode] in
/-- **The piece pairs leg identities exactly as the ambient diagram does.** The slot reindexing
intertwines the piece's leg-level pairing with the ambient one, with no reference to any
enumeration and hence to any times. -/
theorem FixedExternalTwoPointWickDiagram.atomicLegPartner_orderedTwoPointLegMap
    (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (leg : OrderedTwoPointLeg d.1.externalInteractionPart.card) :
    d.atomicLegPartner
        (orderedTwoPointLegMap (d.1.externalInteractionPart.orderEmbOfFin rfl) leg) =
      orderedTwoPointLegMap (d.1.externalInteractionPart.orderEmbOfFin rfl)
        (d.externalPiece.atomicLegPartner leg) := by
  have hsub :
      d.externalPieceLegEquiv.symm
          ((Common.twoPointLegEquiv
            (Finset.univ : Finset (Fin d.1.externalInteractionPart.card))).symm
            (d.externalPiece.atomicLegPartner leg)) =
        d.1.restrictedPartner (d.1.externalComponent 0)
          (d.externalPieceLegEquiv.symm
            ((Common.twoPointLegEquiv
              (Finset.univ : Finset (Fin d.1.externalInteractionPart.card))).symm leg)) := by
    simp only [FixedExternalTwoPointWickDiagram.atomicLegPartner, Equiv.symm_apply_apply]
    rw [Equiv.symm_apply_eq, ← d.externalPiece_partner_externalPieceLegEquiv,
      Equiv.apply_symm_apply]
  rw [← d.twoPointLegEquiv_externalPieceLegEquiv_symm leg,
    ← d.twoPointLegEquiv_externalPieceLegEquiv_symm (d.externalPiece.atomicLegPartner leg),
    hsub, FixedExternalTwoPointWickDiagram.atomicLegPartner, Equiv.symm_apply_apply,
    Common.TwoPointDiagram.restrictedPartner_val]

/-- The times the piece inherits: the ambient times at the slots the external component owns, read
in increasing slot order. -/
noncomputable def FixedExternalTwoPointWickDiagram.externalPieceTimes
    (d : FixedExternalTwoPointWickDiagram Mode n i j) (σ : Fin n → ℝ) :
    Fin d.1.externalInteractionPart.card → ℝ :=
  σ ∘ d.1.externalInteractionPart.orderEmbOfFin rfl

/-- The ambient mixed position of the leg the piece stores at a given mixed position of its own. -/
noncomputable def FixedExternalTwoPointWickDiagram.externalPieceMixedPosition
    (d : FixedExternalTwoPointWickDiagram Mode n i j) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (p : Fin (2 * (2 * d.1.externalInteractionPart.card + 1))) : Fin (2 * (2 * n + 1)) :=
  mixedTimeOrderedAtomicLegPosition τ τ' σ
    (orderedTwoPointLegMap (d.1.externalInteractionPart.orderEmbOfFin rfl)
      (mixedTimeOrderedAtomicLegEquiv τ τ' (d.externalPieceTimes σ) p))

omit [LinearOrder Mode] [Fintype Mode] in
/-- **The piece reads its own mixed order off the ambient one.** The piece's mixed positions sit
inside the ambient mixed positions order-preservingly, with no hypothesis on the times: the slots are
enumerated in increasing order, so the equal-time tie-breaks agree. -/
theorem FixedExternalTwoPointWickDiagram.externalPieceMixedPosition_strictMono
    (d : FixedExternalTwoPointWickDiagram Mode n i j) (τ τ' : ℝ) (σ : Fin n → ℝ) :
    StrictMono (d.externalPieceMixedPosition τ τ' σ) := by
  intro p q hpq
  rw [FixedExternalTwoPointWickDiagram.externalPieceMixedPosition,
    FixedExternalTwoPointWickDiagram.externalPieceMixedPosition,
    mixedTimeOrderedAtomicLegPosition_map_lt_iff
      (d.1.externalInteractionPart.orderEmbOfFin rfl).strictMono]
  simpa [FixedExternalTwoPointWickDiagram.externalPieceTimes,
    mixedTimeOrderedAtomicLegPosition] using hpq

omit [LinearOrder Mode] [Fintype Mode] in
/-- Distinct mixed positions of the piece are distinct ambient mixed positions. -/
theorem FixedExternalTwoPointWickDiagram.externalPieceMixedPosition_injective
    (d : FixedExternalTwoPointWickDiagram Mode n i j) (τ τ' : ℝ) (σ : Fin n → ℝ) :
    Function.Injective (d.externalPieceMixedPosition τ τ' σ) :=
  (d.externalPieceMixedPosition_strictMono τ τ' σ).injective

omit [LinearOrder Mode] [Fintype Mode] in
/-- **The piece stores at each of its mixed positions the leg the ambient diagram stores at the
corresponding ambient position**, up to the slot reindexing. -/
theorem FixedExternalTwoPointWickDiagram.mixedTimeOrderedAtomicLegEquiv_externalPieceMixedPosition
    (d : FixedExternalTwoPointWickDiagram Mode n i j) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (p : Fin (2 * (2 * d.1.externalInteractionPart.card + 1))) :
    mixedTimeOrderedAtomicLegEquiv τ τ' σ (d.externalPieceMixedPosition τ τ' σ p) =
      orderedTwoPointLegMap (d.1.externalInteractionPart.orderEmbOfFin rfl)
        (mixedTimeOrderedAtomicLegEquiv τ τ' (d.externalPieceTimes σ) p) := by
  rw [FixedExternalTwoPointWickDiagram.externalPieceMixedPosition,
    mixedTimeOrderedAtomicLegEquiv_mixedTimeOrderedAtomicLegPosition]

omit [LinearOrder Mode] [Fintype Mode] in
/-- The piece's mixed positions land in the external component. -/
theorem FixedExternalTwoPointWickDiagram.mixedPositionComponent_externalPieceMixedPosition
    (d : FixedExternalTwoPointWickDiagram Mode n i j) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (p : Fin (2 * (2 * d.1.externalInteractionPart.card + 1))) :
    d.mixedPositionComponent τ τ' σ (d.externalPieceMixedPosition τ τ' σ p) =
      d.1.externalComponentPart := by
  have hleg := d.mixedTimeOrderedAtomicLegEquiv_externalPieceMixedPosition τ τ' σ p
  rw [d.mixedPositionComponent_eq_iff_legInComponent,
    d.1.legInComponent_iff_unflattened, twoPointLegEquiv_mixedTimeAmbientPositionEquiv,
    hleg, ← d.externalLegDataEquiv_symm_twoPointLegDataCongr]
  exact (d.1.externalLegDataEquiv.symm
    (Common.twoPointLegDataCongr d.externalSlotEquiv.symm
      (mixedTimeOrderedAtomicLegEquiv τ τ' (d.externalPieceTimes σ) p))).2

/-- **The piece's mixed positions are exactly the external component's mixed positions.** They embed
injectively, and there are as many of them as the component owns. -/
noncomputable def FixedExternalTwoPointWickDiagram.externalPieceMixedPositionEquiv
    (d : FixedExternalTwoPointWickDiagram Mode n i j) (τ τ' : ℝ) (σ : Fin n → ℝ) :
    Fin (2 * (2 * d.1.externalInteractionPart.card + 1)) ≃
      d.MixedComponentPosition τ τ' σ d.1.externalComponentPart :=
  Equiv.ofBijective
    (fun p => ⟨d.externalPieceMixedPosition τ τ' σ p,
      d.mixedPositionComponent_externalPieceMixedPosition τ τ' σ p⟩)
    (by
      have hcard :
          Fintype.card (Fin (2 * (2 * d.1.externalInteractionPart.card + 1))) =
            Fintype.card (d.MixedComponentPosition τ τ' σ d.1.externalComponentPart) := by
        rw [Fintype.card_congr (d.mixedExternalPositionEquiv τ τ' σ), Fintype.card_fin,
          Fintype.card_fin]
        rfl
      refine (Fintype.bijective_iff_injective_and_card _).2 ⟨fun p q h => ?_, hcard⟩
      exact d.externalPieceMixedPosition_injective τ τ' σ (congrArg Subtype.val h))

omit [LinearOrder Mode] [Fintype Mode] in
@[simp]
theorem FixedExternalTwoPointWickDiagram.externalPieceMixedPositionEquiv_apply
    (d : FixedExternalTwoPointWickDiagram Mode n i j) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (p : Fin (2 * (2 * d.1.externalInteractionPart.card + 1))) :
    (d.externalPieceMixedPositionEquiv τ τ' σ p : Fin (2 * (2 * n + 1))) =
      d.externalPieceMixedPosition τ τ' σ p := rfl

omit [LinearOrder Mode] [Fintype Mode] in
/-- **The piece's mixed pairing is the ambient one restricted.** The embedding of the piece's mixed
positions into the ambient ones intertwines the two mixed-order partners, the piece being evaluated
at the times it inherits. -/
theorem FixedExternalTwoPointWickDiagram.externalPieceMixedPosition_partner
    (d : FixedExternalTwoPointWickDiagram Mode n i j) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (p : Fin (2 * (2 * d.1.externalInteractionPart.card + 1))) :
    (d.pairingInMixedOrder τ τ' σ).partner (d.externalPieceMixedPosition τ τ' σ p) =
      d.externalPieceMixedPosition τ τ' σ
        ((d.externalPiece.pairingInMixedOrder τ τ' (d.externalPieceTimes σ)).partner p) := by
  rw [FixedExternalTwoPointWickDiagram.externalPieceMixedPosition,
    FixedExternalTwoPointWickDiagram.externalPieceMixedPosition,
    d.pairingInMixedOrder_partner_legPosition,
    d.atomicLegPartner_orderedTwoPointLegMap,
    d.externalPiece.pairingInMixedOrder_partner_eq_atomicLegPartner,
    mixedTimeOrderedAtomicLegEquiv_mixedTimeOrderedAtomicLegPosition]

end Fermionic
end SecondQuantization
