import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.SlotSplit.SlotLegSplitting
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.External.ExternalConnectivity

set_option linter.style.header false

/-!
# Every two-point diagram splits along its external component

`TwoPointDiagram.slotSplitEquiv` takes apart any diagram whose pairing is split by
`slotLegSplitting`, but says nothing about which diagrams those are. This module supplies the
missing input: instantiating the slot set at the external component's interaction vertices always
works, because a contraction never joins the external component to a vacuum component.

The consequence is the binary decomposition itself — every two-point diagram is an externally
connected piece together with one possibly disconnected vacuum piece, and reassembling them returns
the diagram.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*} {N : ℕ}

/-- The slot leg splitting at the external component's interaction vertices. -/
noncomputable def TwoPointDiagram.externalSlotLegSplitting {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    Combinatorics.PositionSplitting
      (2 * (TwoPointDiagram.interactionPart (d.externalComponent 0)).card + 1)
      (2 * (S \ TwoPointDiagram.interactionPart (d.externalComponent 0)).card)
      (2 * S.card + 1) :=
  slotLegSplitting (TwoPointDiagram.interactionPart_subset (d.externalComponent 0))

/-- An external leg of the piece is the corresponding ambient external leg. -/
theorem TwoPointDiagram.externalSlotLegSplitting_external {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) (e : Fin 2) :
    d.externalSlotLegSplitting (Sum.inl ((twoPointLegEquiv
        (TwoPointDiagram.interactionPart (d.externalComponent 0))).symm (Sum.inl e))) =
      (twoPointLegEquiv S).symm (Sum.inl e) :=
  slotLegSplitting_external _ e

/-- An interaction leg of the piece is the corresponding ambient interaction leg. -/
theorem TwoPointDiagram.externalSlotLegSplitting_interaction {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (v : ↥(TwoPointDiagram.interactionPart (d.externalComponent 0))) (l : Fin 4) :
    d.externalSlotLegSplitting (Sum.inl ((twoPointLegEquiv
        (TwoPointDiagram.interactionPart (d.externalComponent 0))).symm (Sum.inr (v, l)))) =
      (twoPointLegEquiv S).symm
        (Sum.inr (⟨v.1, TwoPointDiagram.interactionPart_subset (d.externalComponent 0) v.2⟩, l)) :=
  slotLegSplitting_left_interaction _ v l

/-- The left part consists of external-component legs. -/
private theorem TwoPointDiagram.legInComponent_externalSlotLegSplitting_inl
    {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (i : Fin (2 * (2 * (TwoPointDiagram.interactionPart (d.externalComponent 0)).card + 1))) :
    d.legInComponent (d.externalComponentPart : Finset (TwoPointVertex S))
      (d.externalSlotLegSplitting (Sum.inl i)) := by
  obtain ⟨x, rfl⟩ := (twoPointLegEquiv
    (TwoPointDiagram.interactionPart (d.externalComponent 0))).symm.surjective i
  refine (d.legInComponent_iff_unflattened d.externalComponentPart _).2 ?_
  cases x with
  | inl e =>
      rw [d.externalSlotLegSplitting_external, Equiv.apply_symm_apply]
      exact d.externalVertex_mem_externalComponentPart e
  | inr p =>
      obtain ⟨v, l⟩ := p
      rw [d.externalSlotLegSplitting_interaction, Equiv.apply_symm_apply]
      exact (TwoPointDiagram.mem_interactionPart_subtype (d.externalComponent 0)
        ⟨v.1, TwoPointDiagram.interactionPart_subset (d.externalComponent 0) v.2⟩).1 v.2

/-- Every external-component leg comes from the left part. -/
private theorem TwoPointDiagram.exists_externalSlotLegSplitting_inl {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (leg : Fin (2 * (2 * S.card + 1)))
    (hleg : d.legInComponent (d.externalComponentPart : Finset (TwoPointVertex S)) leg) :
    ∃ i, d.externalSlotLegSplitting (Sum.inl i) = leg := by
  obtain ⟨x, rfl⟩ := (twoPointLegEquiv S).symm.surjective leg
  rw [d.legInComponent_iff_unflattened d.externalComponentPart, Equiv.apply_symm_apply] at hleg
  cases x with
  | inl e =>
      exact ⟨(twoPointLegEquiv _).symm (Sum.inl e), d.externalSlotLegSplitting_external e⟩
  | inr p =>
      obtain ⟨v, l⟩ := p
      have hv : (v : Fin N) ∈ TwoPointDiagram.interactionPart (d.externalComponent 0) :=
        (TwoPointDiagram.mem_interactionPart_subtype (d.externalComponent 0) v).2 hleg
      refine ⟨(twoPointLegEquiv _).symm (Sum.inr (⟨v.1, hv⟩, l)), ?_⟩
      rw [d.externalSlotLegSplitting_interaction]

/-- The canonical left split positions are exactly the ambient legs of the external component. -/
noncomputable def TwoPointDiagram.externalComponentLegEquiv {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    Fin (2 * (2 * (TwoPointDiagram.interactionPart (d.externalComponent 0)).card + 1)) ≃
      {leg : Fin (2 * (2 * S.card + 1)) //
        d.legInComponent (d.externalComponentPart : Finset (TwoPointVertex S)) leg} :=
  Equiv.ofBijective
    (fun i => ⟨d.externalSlotLegSplitting (Sum.inl i),
      d.legInComponent_externalSlotLegSplitting_inl i⟩)
    ⟨by
      intro a b h
      have h' : Sum.inl a = Sum.inl b :=
        d.externalSlotLegSplitting.injective (congrArg Subtype.val h)
      exact Sum.inl.inj h',
     by
      intro leg
      obtain ⟨i, hi⟩ := d.exists_externalSlotLegSplitting_inl leg.1 leg.2
      exact ⟨i, Subtype.ext hi⟩⟩

@[simp]
theorem TwoPointDiagram.externalComponentLegEquiv_apply {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (i : Fin (2 * (2 * (TwoPointDiagram.interactionPart (d.externalComponent 0)).card + 1))) :
    (d.externalComponentLegEquiv i : Fin (2 * (2 * S.card + 1))) =
      d.externalSlotLegSplitting (Sum.inl i) :=
  rfl

/-- **The pairing of a two-point diagram is split by its external component's slot splitting.**

A contraction never joins the external component to a vacuum component, so the legs coming from the
left part are closed under the partner map. -/
theorem TwoPointDiagram.isSplit_externalSlotLegSplitting {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    d.pairing.IsSplit d.externalSlotLegSplitting := by
  intro i
  have h2 : d.legInComponent (d.externalComponentPart : Finset (TwoPointVertex S))
      (d.pairing.partner (d.externalSlotLegSplitting (Sum.inl i))) :=
    (d.legInComponent_partner_iff (d.externalComponentPart : Finset (TwoPointVertex S)) _).1
      (d.legInComponent_externalSlotLegSplitting_inl i)
  obtain ⟨j, hj⟩ := d.exists_externalSlotLegSplitting_inl _ h2
  exact ⟨j, hj.symm⟩

/-- **The binary external/vacuum decomposition of a two-point diagram.**

The external piece carries the two external legs and the interaction vertices of their component;
the vacuum piece carries all the others and is in general disconnected. -/
noncomputable def TwoPointDiagram.externalVacuumSplit {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    TwoPointDiagram ExternalLabel InternalLabel N
        (TwoPointDiagram.interactionPart (d.externalComponent 0)) ×
      QuarticDiagram InternalLabel N (S \ TwoPointDiagram.interactionPart (d.externalComponent 0)) :=
  TwoPointDiagram.slotSplitEquiv (TwoPointDiagram.interactionPart_subset (d.externalComponent 0))
    ⟨d, d.isSplit_externalSlotLegSplitting⟩

/-- The canonical external split piece preserves the ambient external labels. -/
@[simp]
theorem TwoPointDiagram.externalVacuumSplit_fst_externalLabel {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    d.externalVacuumSplit.1.externalLabel = d.externalLabel :=
  rfl

/-- The canonical external split piece reads each interaction label from the corresponding ambient
slot. -/
@[simp]
theorem TwoPointDiagram.externalVacuumSplit_fst_vertexLabel {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (v : ↥(TwoPointDiagram.interactionPart (d.externalComponent 0))) :
    d.externalVacuumSplit.1.vertexLabel v =
      d.vertexLabel ⟨v.1, TwoPointDiagram.interactionPart_subset
        (d.externalComponent 0) v.2⟩ :=
  rfl

/-- The canonical external split pairing is read directly from the ambient partner map along the
left slot embedding. -/
theorem TwoPointDiagram.externalVacuumSplit_fst_partner {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (i : Fin (2 * (2 * (TwoPointDiagram.interactionPart (d.externalComponent 0)).card + 1))) :
    d.pairing.partner (d.externalSlotLegSplitting (Sum.inl i)) =
      d.externalSlotLegSplitting (Sum.inl (d.externalVacuumSplit.1.pairing.partner i)) := by
  exact Pairing.partner_splitLeft d.externalSlotLegSplitting
    d.isSplit_externalSlotLegSplitting i

/-- The canonical external leg equivalence intertwines the split pairing with the ambient restricted
partner on the external component. -/
private theorem TwoPointDiagram.externalComponentLegEquiv_partner {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (i : Fin (2 * (2 * (TwoPointDiagram.interactionPart (d.externalComponent 0)).card + 1))) :
    d.externalComponentLegEquiv (d.externalVacuumSplit.1.pairing.partner i) =
      d.restrictedPartner (d.externalComponentPart : Finset (TwoPointVertex S))
        (d.externalComponentLegEquiv i) := by
  apply Subtype.ext
  rw [d.restrictedPartner_val]
  exact (d.externalVacuumSplit_fst_partner i).symm

@[simp]
theorem TwoPointDiagram.externalComponentLegEquiv_symm_restrictedPartner
    {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (leg : {leg : Fin (2 * (2 * S.card + 1)) //
      d.legInComponent (d.externalComponentPart : Finset (TwoPointVertex S)) leg}) :
    d.externalComponentLegEquiv.symm
        (d.restrictedPartner (d.externalComponentPart : Finset (TwoPointVertex S)) leg) =
      d.externalVacuumSplit.1.pairing.partner (d.externalComponentLegEquiv.symm leg) := by
  rw [Equiv.symm_apply_eq, d.externalComponentLegEquiv_partner, Equiv.apply_symm_apply]

/-- **Reassembling the two pieces returns the diagram.** -/
theorem TwoPointDiagram.ofSlotSplit_externalVacuumSplit {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    TwoPointDiagram.ofSlotSplit (TwoPointDiagram.interactionPart_subset (d.externalComponent 0))
        d.externalVacuumSplit.1 d.externalVacuumSplit.2 = d :=
  TwoPointDiagram.ofSlotSplit_slotSplit _ d d.isSplit_externalSlotLegSplitting

end Common
end SecondQuantization
