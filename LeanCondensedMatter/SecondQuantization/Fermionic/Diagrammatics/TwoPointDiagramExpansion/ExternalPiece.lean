import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedLegSlotEmbedding
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedPositionLeg
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ComponentDecomposition
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.SlotCongr
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ComponentOrderedSimplex
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ComponentVertexProduct
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ExternalSlotSplit

set_option linter.style.header false

/-!
# The external component as a standalone two-point diagram

The canonical external/vacuum slot split leaves the interaction vertices of the external piece
indexed by the ambient slots that component owns. The linked-cluster factorization needs the same
data as a diagram in its own right, on as many slots as the component owns, since that is the shape
a perturbative coefficient is summed over.

This module performs that reindexing on the Common-owned slot set
`TwoPointDiagram.externalInteractionPart`. The slots use Common's canonical increasing
`standardSlotEquiv`, which is what makes the piece's mixed event and leg orders agree with the
ambient ones; see `MixedEventSlotEmbedding` and `MixedLegSlotEmbedding` for that comparison. The
piece keeps the ambient external labels, so it is again a fixed-external diagram for the same two
modes.

The last results identify the piece's legs with the ambient component's legs — using the canonical
Common `externalComponentLegEquiv` followed by that same slot standardization — and show that the
piece pairs exactly the legs the ambient diagram pairs, both as flattened positions and as the leg
identities `atomicLegPartner` pairs, the latter carrying no reference to the times.
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

/-- **The external component as a standalone fixed-external two-point diagram**, obtained from the
left half of the canonical external/vacuum slot split and then relabeled onto consecutive slots. -/
noncomputable def FixedExternalTwoPointWickDiagram.externalPiece
    (d : FixedExternalTwoPointWickDiagram Mode n i j) :
    FixedExternalTwoPointWickDiagram Mode d.1.externalInteractionPart.card i j :=
  ⟨d.1.externalVacuumSplit.1.slotCongr
      (Common.standardSlotEquiv d.1.externalInteractionPart), by
    rw [Common.TwoPointDiagram.slotCongr_externalLabel,
      Common.TwoPointDiagram.externalVacuumSplit_fst_externalLabel]
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
  rw [Common.TwoPointDiagram.slotCongr_vertexLabel,
    Common.TwoPointDiagram.externalVacuumSplit_fst_vertexLabel]
  exact congrArg d.1.vertexLabel
    (Subtype.ext (Common.standardSlotEquiv_symm_coe d.1.externalInteractionPart
      ⟨v, Finset.mem_univ v⟩))

/-- The flattened legs of the standalone piece are the canonical Common external-component legs,
followed by the canonical increasing slot standardization. This is an implementation detail of the
semantic transport results. -/
private noncomputable def FixedExternalTwoPointWickDiagram.externalPieceLegEquiv
    (d : FixedExternalTwoPointWickDiagram Mode n i j) :
    {leg : Fin (2 * (2 * (Finset.univ : Finset (Fin n)).card + 1)) //
        d.1.legInComponent d.1.externalComponentPart leg} ≃
      Fin (2 * (2 *
        (Finset.univ : Finset (Fin d.1.externalInteractionPart.card)).card + 1)) :=
  d.1.externalComponentLegEquiv.symm.trans
    (Common.twoPointLegCongr (Common.standardSlotEquiv d.1.externalInteractionPart))

omit [LinearOrder Mode] [Fintype Mode] in
/-- **The piece pairs the legs the ambient diagram pairs.** This is the canonical Common external
component leg transport followed by `slotCongr`; no Fermionic copy of that equivalence is built. -/
private theorem FixedExternalTwoPointWickDiagram.externalPiece_partner_externalPieceLegEquiv
    (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (leg : {leg : Fin (2 * (2 * (Finset.univ : Finset (Fin n)).card + 1)) //
      d.1.legInComponent d.1.externalComponentPart leg}) :
    d.externalPiece.1.pairing.partner (d.externalPieceLegEquiv leg) =
      d.externalPieceLegEquiv (d.1.restrictedPartner d.1.externalComponentPart leg) := by
  change
    (d.1.externalVacuumSplit.1.slotCongr
      (Common.standardSlotEquiv d.1.externalInteractionPart)).pairing.partner
        (Common.twoPointLegCongr (Common.standardSlotEquiv d.1.externalInteractionPart)
          (d.1.externalComponentLegEquiv.symm leg)) =
      Common.twoPointLegCongr (Common.standardSlotEquiv d.1.externalInteractionPart)
        (d.1.externalComponentLegEquiv.symm
          (d.1.restrictedPartner d.1.externalComponentPart leg))
  rw [Common.TwoPointDiagram.slotCongr_partner,
    d.1.externalComponentLegEquiv_symm_restrictedPartner]
  rfl

omit [LinearOrder Mode] [Fintype Mode] in
private theorem FixedExternalTwoPointWickDiagram.externalSlotLegSplitting_external_externalPart
    (d : FixedExternalTwoPointWickDiagram Mode n i j) (e : Fin 2) :
    d.1.externalSlotLegSplitting
        (Sum.inl ((Common.twoPointLegEquiv d.1.externalInteractionPart).symm (Sum.inl e))) =
      (Common.twoPointLegEquiv (Finset.univ : Finset (Fin n))).symm (Sum.inl e) := by
  convert d.1.externalSlotLegSplitting_external e using 1
  · simp only [Common.TwoPointDiagram.externalInteractionPart]
    apply Fin.ext
    rfl

omit [LinearOrder Mode] [Fintype Mode] in
private theorem FixedExternalTwoPointWickDiagram.externalSlotLegSplitting_interaction_externalPart
    (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (v : ↥d.1.externalInteractionPart) (l : Fin 4) :
    d.1.externalSlotLegSplitting
        (Sum.inl ((Common.twoPointLegEquiv d.1.externalInteractionPart).symm
          (Sum.inr (v, l)))) =
      (Common.twoPointLegEquiv (Finset.univ : Finset (Fin n))).symm
        (Sum.inr (⟨v.1, Finset.mem_univ _⟩, l)) := by
  convert d.1.externalSlotLegSplitting_interaction v l using 1
  · simp only [Common.TwoPointDiagram.externalInteractionPart]
    apply Fin.ext
    rfl

omit [LinearOrder Mode] [Fintype Mode] in
/-- Reading a standalone-piece leg through the canonical split gives exactly the ambient leg named
by the increasing interaction-slot embedding. -/
private theorem FixedExternalTwoPointWickDiagram.twoPointLegEquiv_externalPieceLegEquiv_symm
    (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (leg : OrderedTwoPointLeg d.1.externalInteractionPart.card) :
    Common.twoPointLegEquiv (Finset.univ : Finset (Fin n))
        ((d.externalPieceLegEquiv.symm
          ((Common.twoPointLegEquiv
            (Finset.univ : Finset (Fin d.1.externalInteractionPart.card))).symm leg)).1) =
      orderedTwoPointLegMap (d.1.externalInteractionPart.orderEmbOfFin rfl) leg := by
  let e := Common.standardSlotEquiv d.1.externalInteractionPart
  have hcongr (x : OrderedTwoPointLeg d.1.externalInteractionPart.card) :
      Common.twoPointLegEquiv d.1.externalInteractionPart
          ((Common.twoPointLegCongr e).symm
            ((Common.twoPointLegEquiv
              (Finset.univ : Finset (Fin d.1.externalInteractionPart.card))).symm x)) =
        Common.twoPointLegDataCongr e.symm x := by
    rw [← Common.twoPointLegCongr_symm, Common.twoPointLegCongr_eq_trans,
      Equiv.trans_apply, Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hunfold :
      ((d.externalPieceLegEquiv.symm
          ((Common.twoPointLegEquiv
            (Finset.univ : Finset (Fin d.1.externalInteractionPart.card))).symm leg)).1 :
        Fin (2 * (2 * (Finset.univ : Finset (Fin n)).card + 1))) =
      d.1.externalSlotLegSplitting
        (Sum.inl ((Common.twoPointLegCongr e).symm
          ((Common.twoPointLegEquiv
            (Finset.univ : Finset (Fin d.1.externalInteractionPart.card))).symm leg))) := rfl
  rw [hunfold]
  cases leg with
  | inl ext =>
      have hk :
          (Common.twoPointLegCongr e).symm
              ((Common.twoPointLegEquiv
                (Finset.univ : Finset (Fin d.1.externalInteractionPart.card))).symm
                  (Sum.inl ext)) =
            (Common.twoPointLegEquiv d.1.externalInteractionPart).symm (Sum.inl ext) := by
        have h := hcongr (Sum.inl ext)
        rw [Common.twoPointLegDataCongr_inl, Equiv.apply_eq_iff_eq_symm_apply] at h
        exact h
      rw [hk, d.externalSlotLegSplitting_external_externalPart, Equiv.apply_symm_apply]
      rfl
  | inr p =>
      obtain ⟨v, l⟩ := p
      have hk :
          (Common.twoPointLegCongr e).symm
              ((Common.twoPointLegEquiv
                (Finset.univ : Finset (Fin d.1.externalInteractionPart.card))).symm
                  (Sum.inr (v, l))) =
            (Common.twoPointLegEquiv d.1.externalInteractionPart).symm
              (Sum.inr (e.symm v, l)) := by
        have h := hcongr (Sum.inr (v, l))
        rw [Common.twoPointLegDataCongr_inr, Equiv.apply_eq_iff_eq_symm_apply] at h
        exact h
      rw [hk, d.externalSlotLegSplitting_interaction_externalPart, Equiv.apply_symm_apply]
      apply congrArg Sum.inr
      apply Prod.ext
      · exact Subtype.ext (Common.standardSlotEquiv_symm_coe d.1.externalInteractionPart v)
      · rfl

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
        d.1.restrictedPartner d.1.externalComponentPart
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
  let pieceLeg := mixedTimeOrderedAtomicLegEquiv τ τ' (d.externalPieceTimes σ) p
  let ambientLeg := d.externalPieceLegEquiv.symm
    ((Common.twoPointLegEquiv
      (Finset.univ : Finset (Fin d.1.externalInteractionPart.card))).symm pieceLeg)
  have hleg := d.mixedTimeOrderedAtomicLegEquiv_externalPieceMixedPosition τ τ' σ p
  have hcanonical := d.twoPointLegEquiv_externalPieceLegEquiv_symm pieceLeg
  have hamb :
      d.1.unflattenedLegInComponent d.1.externalComponentPart
        (Common.twoPointLegEquiv (Finset.univ : Finset (Fin n)) ambientLeg.1) :=
    (d.1.legInComponent_iff_unflattened d.1.externalComponentPart ambientLeg.1).1 ambientLeg.2
  rw [d.mixedPositionComponent_eq_iff_legInComponent,
    d.1.legInComponent_iff_unflattened, twoPointLegEquiv_mixedTimeAmbientPositionEquiv,
    hleg, ← hcanonical]
  exact hamb

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
