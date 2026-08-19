import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Mixed.MixedOrderPairing
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ComponentOrderedSimplex
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.SlotCongr
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.External.ExternalSlotSplit

set_option linter.style.header false

/-!
# The external component as a standalone two-point diagram

A full two-point diagram has one canonical component containing both external vertices.  Restricting
to that component produces a two-point diagram whose interaction slots are still indexed by the
ambient slot subset.  This module standardizes those slots onto consecutive `Fin` indices and records
the induced transport of atomic legs, mixed-time positions, component positions, and pair partners.

Everything here is structural: it depends only on the Common two-point diagram, its pairing-induced
components, and the Common mixed-time ordering.  There is no particle-statistics choice, operator
realization, Gibbs contraction, or physical amplitude.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*} {n : ℕ}

/-- The external component owns as many interaction slots as its component-local ordered simplex. -/
theorem TwoPointDiagram.externalInteractionPart_card
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n))) :
    d.externalInteractionPart.card = d.interactionComponentSize d.externalComponentPart := rfl

/-- The canonical external component as a standalone two-point diagram on consecutive slots. -/
noncomputable def TwoPointDiagram.externalPiece
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n))) :
    TwoPointDiagram ExternalLabel InternalLabel d.externalInteractionPart.card
      (Finset.univ : Finset (Fin d.externalInteractionPart.card)) :=
  d.externalVacuumSplit.1.slotCongr (standardSlotEquiv d.externalInteractionPart)

@[simp]
theorem TwoPointDiagram.externalPiece_externalLabel
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n))) :
    d.externalPiece.externalLabel = d.externalLabel := rfl

@[simp]
theorem TwoPointDiagram.externalPiece_vertexLabel
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (v : Fin d.externalInteractionPart.card) :
    d.externalPiece.vertexLabel ⟨v, Finset.mem_univ _⟩ =
      d.vertexLabel ⟨d.externalInteractionPart.orderEmbOfFin rfl v, Finset.mem_univ _⟩ := by
  unfold TwoPointDiagram.externalPiece
  rw [TwoPointDiagram.slotCongr_vertexLabel,
    TwoPointDiagram.externalVacuumSplit_fst_vertexLabel]
  exact congrArg d.vertexLabel
    (Subtype.ext (standardSlotEquiv_symm_coe d.externalInteractionPart
      ⟨v, Finset.mem_univ v⟩))

private noncomputable def TwoPointDiagram.externalPieceLegEquiv
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n))) :
    {leg : Fin (2 * (2 * (Finset.univ : Finset (Fin n)).card + 1)) //
        d.legInComponent d.externalComponentPart leg} ≃
      Fin (2 * (2 *
        (Finset.univ : Finset (Fin d.externalInteractionPart.card)).card + 1)) :=
  d.externalComponentLegEquiv.symm.trans
    (twoPointLegCongr (standardSlotEquiv d.externalInteractionPart))

private theorem TwoPointDiagram.externalPiece_partner_externalPieceLegEquiv
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (leg : {leg : Fin (2 * (2 * (Finset.univ : Finset (Fin n)).card + 1)) //
      d.legInComponent d.externalComponentPart leg}) :
    d.externalPiece.pairing.partner (d.externalPieceLegEquiv leg) =
      d.externalPieceLegEquiv (d.restrictedPartner d.externalComponentPart leg) := by
  change
    (d.externalVacuumSplit.1.slotCongr
      (standardSlotEquiv d.externalInteractionPart)).pairing.partner
        (twoPointLegCongr (standardSlotEquiv d.externalInteractionPart)
          (d.externalComponentLegEquiv.symm leg)) =
      twoPointLegCongr (standardSlotEquiv d.externalInteractionPart)
        (d.externalComponentLegEquiv.symm
          (d.restrictedPartner d.externalComponentPart leg))
  rw [TwoPointDiagram.slotCongr_partner,
    d.externalComponentLegEquiv_symm_restrictedPartner]
  rfl

private theorem TwoPointDiagram.externalSlotLegSplitting_external_externalPart
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (e : Fin 2) :
    d.externalSlotLegSplitting
        (Sum.inl ((twoPointLegEquiv d.externalInteractionPart).symm (Sum.inl e))) =
      (twoPointLegEquiv (Finset.univ : Finset (Fin n))).symm (Sum.inl e) := by
  convert d.externalSlotLegSplitting_external e using 1
  · simp only [TwoPointDiagram.externalInteractionPart]
    apply Fin.ext
    rfl

private theorem TwoPointDiagram.externalSlotLegSplitting_interaction_externalPart
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (v : ↥d.externalInteractionPart) (l : Fin 4) :
    d.externalSlotLegSplitting
        (Sum.inl ((twoPointLegEquiv d.externalInteractionPart).symm
          (Sum.inr (v, l)))) =
      (twoPointLegEquiv (Finset.univ : Finset (Fin n))).symm
        (Sum.inr (⟨v.1, Finset.mem_univ _⟩, l)) := by
  convert d.externalSlotLegSplitting_interaction v l using 1
  · simp only [TwoPointDiagram.externalInteractionPart]
    apply Fin.ext
    rfl

private theorem TwoPointDiagram.twoPointLegEquiv_externalPieceLegEquiv_symm
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (leg : OrderedTwoPointLeg d.externalInteractionPart.card) :
    twoPointLegEquiv (Finset.univ : Finset (Fin n))
        ((d.externalPieceLegEquiv.symm
          ((twoPointLegEquiv
            (Finset.univ : Finset (Fin d.externalInteractionPart.card))).symm leg)).1) =
      orderedTwoPointLegMap (d.externalInteractionPart.orderEmbOfFin rfl) leg := by
  let e := standardSlotEquiv d.externalInteractionPart
  have hcongr (x : OrderedTwoPointLeg d.externalInteractionPart.card) :
      twoPointLegEquiv d.externalInteractionPart
          ((twoPointLegCongr e).symm
            ((twoPointLegEquiv
              (Finset.univ : Finset (Fin d.externalInteractionPart.card))).symm x)) =
        twoPointLegDataCongr e.symm x := by
    rw [← twoPointLegCongr_symm, twoPointLegCongr_eq_trans,
      Equiv.trans_apply, Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hunfold :
      ((d.externalPieceLegEquiv.symm
          ((twoPointLegEquiv
            (Finset.univ : Finset (Fin d.externalInteractionPart.card))).symm leg)).1 :
        Fin (2 * (2 * (Finset.univ : Finset (Fin n)).card + 1))) =
      d.externalSlotLegSplitting
        (Sum.inl ((twoPointLegCongr e).symm
          ((twoPointLegEquiv
            (Finset.univ : Finset (Fin d.externalInteractionPart.card))).symm leg))) := rfl
  rw [hunfold]
  cases leg with
  | inl ext =>
      have hk :
          (twoPointLegCongr e).symm
              ((twoPointLegEquiv
                (Finset.univ : Finset (Fin d.externalInteractionPart.card))).symm
                  (Sum.inl ext)) =
            (twoPointLegEquiv d.externalInteractionPart).symm (Sum.inl ext) := by
        have h := hcongr (Sum.inl ext)
        rw [twoPointLegDataCongr_inl, Equiv.apply_eq_iff_eq_symm_apply] at h
        exact h
      rw [hk, d.externalSlotLegSplitting_external_externalPart, Equiv.apply_symm_apply]
      rfl
  | inr p =>
      obtain ⟨v, l⟩ := p
      have hk :
          (twoPointLegCongr e).symm
              ((twoPointLegEquiv
                (Finset.univ : Finset (Fin d.externalInteractionPart.card))).symm
                  (Sum.inr (v, l))) =
            (twoPointLegEquiv d.externalInteractionPart).symm
              (Sum.inr (e.symm v, l)) := by
        have h := hcongr (Sum.inr (v, l))
        rw [twoPointLegDataCongr_inr, Equiv.apply_eq_iff_eq_symm_apply] at h
        exact h
      rw [hk, d.externalSlotLegSplitting_interaction_externalPart, Equiv.apply_symm_apply]
      apply congrArg Sum.inr
      apply Prod.ext
      · exact Subtype.ext (standardSlotEquiv_symm_coe d.externalInteractionPart v)
      · rfl

/-- The atomic partner map is natural under the canonical external-piece slot embedding. -/
theorem TwoPointDiagram.atomicLegPartner_orderedTwoPointLegMap
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (leg : OrderedTwoPointLeg d.externalInteractionPart.card) :
    d.atomicLegPartner
        (orderedTwoPointLegMap (d.externalInteractionPart.orderEmbOfFin rfl) leg) =
      orderedTwoPointLegMap (d.externalInteractionPart.orderEmbOfFin rfl)
        (d.externalPiece.atomicLegPartner leg) := by
  have hsub :
      d.externalPieceLegEquiv.symm
          ((twoPointLegEquiv
            (Finset.univ : Finset (Fin d.externalInteractionPart.card))).symm
            (d.externalPiece.atomicLegPartner leg)) =
        d.restrictedPartner d.externalComponentPart
          (d.externalPieceLegEquiv.symm
            ((twoPointLegEquiv
              (Finset.univ : Finset (Fin d.externalInteractionPart.card))).symm leg)) := by
    simp only [TwoPointDiagram.atomicLegPartner, Equiv.symm_apply_apply]
    rw [Equiv.symm_apply_eq, ← d.externalPiece_partner_externalPieceLegEquiv,
      Equiv.apply_symm_apply]
  rw [← d.twoPointLegEquiv_externalPieceLegEquiv_symm leg,
    ← d.twoPointLegEquiv_externalPieceLegEquiv_symm (d.externalPiece.atomicLegPartner leg),
    hsub, TwoPointDiagram.atomicLegPartner, Equiv.symm_apply_apply,
    TwoPointDiagram.restrictedPartner_val]

/-- Restrict ambient interaction times to the canonically ordered slots of the external piece. -/
noncomputable def TwoPointDiagram.externalPieceTimes
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (σ : Fin n → ℝ) : Fin d.externalInteractionPart.card → ℝ :=
  σ ∘ d.externalInteractionPart.orderEmbOfFin rfl

/-- Embed a mixed-order position of the standalone external piece into the ambient mixed order. -/
noncomputable def TwoPointDiagram.externalPieceMixedPosition
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (p : Fin (2 * (2 * d.externalInteractionPart.card + 1))) : Fin (2 * (2 * n + 1)) :=
  mixedTimeOrderedAtomicLegPosition τ τ' σ
    (orderedTwoPointLegMap (d.externalInteractionPart.orderEmbOfFin rfl)
      (mixedTimeOrderedAtomicLegEquiv τ τ' (d.externalPieceTimes σ) p))

theorem TwoPointDiagram.externalPieceMixedPosition_strictMono
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    StrictMono (d.externalPieceMixedPosition τ τ' σ) := by
  intro p q hpq
  rw [TwoPointDiagram.externalPieceMixedPosition,
    TwoPointDiagram.externalPieceMixedPosition,
    mixedTimeOrderedAtomicLegPosition_map_lt_iff
      (d.externalInteractionPart.orderEmbOfFin rfl).strictMono]
  simpa [TwoPointDiagram.externalPieceTimes,
    mixedTimeOrderedAtomicLegPosition] using hpq

theorem TwoPointDiagram.externalPieceMixedPosition_injective
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    Function.Injective (d.externalPieceMixedPosition τ τ' σ) :=
  (d.externalPieceMixedPosition_strictMono τ τ' σ).injective

theorem TwoPointDiagram.mixedTimeOrderedAtomicLegEquiv_externalPieceMixedPosition
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (p : Fin (2 * (2 * d.externalInteractionPart.card + 1))) :
    mixedTimeOrderedAtomicLegEquiv τ τ' σ (d.externalPieceMixedPosition τ τ' σ p) =
      orderedTwoPointLegMap (d.externalInteractionPart.orderEmbOfFin rfl)
        (mixedTimeOrderedAtomicLegEquiv τ τ' (d.externalPieceTimes σ) p) := by
  rw [TwoPointDiagram.externalPieceMixedPosition,
    mixedTimeOrderedAtomicLegEquiv_mixedTimeOrderedAtomicLegPosition]

theorem TwoPointDiagram.mixedPositionComponent_externalPieceMixedPosition
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (p : Fin (2 * (2 * d.externalInteractionPart.card + 1))) :
    d.mixedPositionComponent τ τ' σ (d.externalPieceMixedPosition τ τ' σ p) =
      d.externalComponentPart := by
  let pieceLeg := mixedTimeOrderedAtomicLegEquiv τ τ' (d.externalPieceTimes σ) p
  let ambientLeg := d.externalPieceLegEquiv.symm
    ((twoPointLegEquiv
      (Finset.univ : Finset (Fin d.externalInteractionPart.card))).symm pieceLeg)
  have hleg := d.mixedTimeOrderedAtomicLegEquiv_externalPieceMixedPosition τ τ' σ p
  have hcanonical := d.twoPointLegEquiv_externalPieceLegEquiv_symm pieceLeg
  have hamb :
      d.unflattenedLegInComponent d.externalComponentPart
        (twoPointLegEquiv (Finset.univ : Finset (Fin n)) ambientLeg.1) :=
    (d.legInComponent_iff_unflattened d.externalComponentPart ambientLeg.1).1 ambientLeg.2
  rw [d.mixedPositionComponent_eq_iff_legInComponent,
    d.legInComponent_iff_unflattened, twoPointLegEquiv_mixedTimeAmbientPositionEquiv,
    hleg, ← hcanonical]
  exact hamb

/-- The canonical equivalence between external-piece mixed positions and the ambient external
component's mixed-position fiber. -/
noncomputable def TwoPointDiagram.externalPieceMixedPositionEquiv
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    Fin (2 * (2 * d.externalInteractionPart.card + 1)) ≃
      d.MixedComponentPosition τ τ' σ d.externalComponentPart :=
  Equiv.ofBijective
    (fun p => ⟨d.externalPieceMixedPosition τ τ' σ p,
      d.mixedPositionComponent_externalPieceMixedPosition τ τ' σ p⟩)
    (by
      have hcard :
          Fintype.card (Fin (2 * (2 * d.externalInteractionPart.card + 1))) =
            Fintype.card (d.MixedComponentPosition τ τ' σ d.externalComponentPart) := by
        rw [Fintype.card_congr (d.mixedExternalPositionEquiv τ τ' σ), Fintype.card_fin,
          Fintype.card_fin]
        rfl
      refine (Fintype.bijective_iff_injective_and_card _).2 ⟨fun p q h => ?_, hcard⟩
      exact d.externalPieceMixedPosition_injective τ τ' σ (congrArg Subtype.val h))

@[simp]
theorem TwoPointDiagram.externalPieceMixedPositionEquiv_apply
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (p : Fin (2 * (2 * d.externalInteractionPart.card + 1))) :
    (d.externalPieceMixedPositionEquiv τ τ' σ p : Fin (2 * (2 * n + 1))) =
      d.externalPieceMixedPosition τ τ' σ p := rfl

/-- The mixed-order partner of an external-piece position is transported by the same embedding. -/
theorem TwoPointDiagram.externalPieceMixedPosition_partner
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (p : Fin (2 * (2 * d.externalInteractionPart.card + 1))) :
    (d.pairingInMixedOrder τ τ' σ).partner (d.externalPieceMixedPosition τ τ' σ p) =
      d.externalPieceMixedPosition τ τ' σ
        ((d.externalPiece.pairingInMixedOrder τ τ' (d.externalPieceTimes σ)).partner p) := by
  rw [TwoPointDiagram.externalPieceMixedPosition,
    TwoPointDiagram.externalPieceMixedPosition,
    d.pairingInMixedOrder_partner_legPosition,
    d.atomicLegPartner_orderedTwoPointLegMap,
    d.externalPiece.pairingInMixedOrder_partner_eq_atomicLegPartner,
    mixedTimeOrderedAtomicLegEquiv_mixedTimeOrderedAtomicLegPosition]

end Common
end SecondQuantization
