import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ExternalRestriction

set_option linter.style.header false

/-!
# Connectedness of the restricted external component

Restriction to the component containing the distinguished external vertices preserves its complete
pairing graph. Hence the restricted two-point diagram has no vacuum component and is externally
connected in the two-one-legged-external setup.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*} {N : ℕ}

/-- Vertices of the ambient external component, reindexed as vertices of the restricted two-point
diagram. -/
noncomputable def TwoPointDiagram.externalBlockVertexEquiv {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    {v : TwoPointVertex S // v ∈ d.externalComponent 0} ≃
      TwoPointVertex (TwoPointDiagram.interactionPart (d.externalComponent 0)) where
  toFun v := by
    rcases v with ⟨v, hv⟩
    cases v with
    | inl e => exact Sum.inl e
    | inr w =>
        exact Sum.inr ⟨w.1, (TwoPointDiagram.mem_interactionPart_subtype
          (d.externalComponent 0) w).2 hv⟩
  invFun v := by
    cases v with
    | inl e => exact ⟨Sum.inl e, d.externalVertex_mem_externalComponentPart e⟩
    | inr w =>
        let vS : ↥S := ⟨w.1, TwoPointDiagram.interactionPart_subset
          (d.externalComponent 0) w.2⟩
        exact ⟨Sum.inr vS,
          (TwoPointDiagram.mem_interactionPart_subtype
            (d.externalComponent 0) vS).1 w.2⟩
  left_inv v := by
    rcases v with ⟨(e | w), hv⟩
    · apply Subtype.ext
      rfl
    · apply Subtype.ext
      rfl
  right_inv v := by
    rcases v with e | w
    · rfl
    · apply congrArg Sum.inr
      exact Subtype.ext (by rfl)

/-- The flattened external-block reindexing has the expected unflattened leg value. -/
theorem TwoPointDiagram.twoPointLegEquiv_externalBlockLegEquiv
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (leg : {leg : Fin (2 * (2 * S.card + 1)) //
      d.legInComponent (d.externalComponent 0) leg}) :
    twoPointLegEquiv (TwoPointDiagram.interactionPart (d.externalComponent 0))
        (d.externalBlockLegEquiv leg) =
      d.externalLegDataEquiv
        ⟨twoPointLegEquiv S leg.1,
          (d.legInComponent_iff_unflattened d.externalComponentPart leg.1).1 leg.2⟩ := by
  change twoPointLegEquiv (TwoPointDiagram.interactionPart (d.externalComponent 0))
      ((twoPointLegEquiv (TwoPointDiagram.interactionPart (d.externalComponent 0))).symm
        (d.externalLegDataEquiv
          (((twoPointLegEquiv S).subtypeEquiv fun p =>
            d.legInComponent_iff_unflattened d.externalComponentPart p) leg))) = _
  rw [Equiv.apply_symm_apply]
  apply d.externalLegDataEquiv.injective
  apply Subtype.ext
  rfl

/-- Restricting an unflattened leg and then taking its vertex agrees with restricting its vertex. -/
theorem TwoPointDiagram.twoPointLegVertex_externalLegDataEquiv
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (leg : {leg : TwoPointLeg S //
      d.unflattenedLegInComponent d.externalComponentPart leg}) :
    twoPointLegVertex (d.externalLegDataEquiv leg) =
      d.externalBlockVertexEquiv ⟨twoPointLegVertex leg.1, leg.2⟩ := by
  rcases leg with ⟨e | ⟨v, l⟩, hleg⟩
  · rfl
  · rfl

/-- The external-component leg reindexing and vertex reindexing commute. -/
theorem TwoPointDiagram.twoPointVertexOfLeg_externalBlockLegEquiv
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (leg : {leg : Fin (2 * (2 * S.card + 1)) //
      d.legInComponent (d.externalComponent 0) leg}) :
    twoPointVertexOfLeg (d.externalBlockLegEquiv leg) =
      d.externalBlockVertexEquiv
        ⟨twoPointVertexOfLeg leg.1,
          (d.legInComponent_iff_vertex_mem d.externalComponentPart.2 leg.1).1 leg.2⟩ := by
  change twoPointLegVertex
      (twoPointLegEquiv (TwoPointDiagram.interactionPart (d.externalComponent 0))
        (d.externalBlockLegEquiv leg)) = _
  rw [d.twoPointLegEquiv_externalBlockLegEquiv leg]
  exact d.twoPointLegVertex_externalLegDataEquiv
    ⟨twoPointLegEquiv S leg.1,
      (d.legInComponent_iff_unflattened d.externalComponentPart leg.1).1 leg.2⟩

/-- An ambient edge whose endpoints lie in the external component becomes an edge of the restricted
external diagram. -/
theorem TwoPointDiagram.restrictExternalComponent_adj
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (v w : {v : TwoPointVertex S // v ∈ d.externalComponent 0})
    (hvw : d.vertexGraph.Adj v.1 w.1) :
    d.restrictExternalComponent.vertexGraph.Adj
      (d.externalBlockVertexEquiv v) (d.externalBlockVertexEquiv w) := by
  rcases hvw with ⟨hne, leg, hv, hw⟩
  have hleg : d.legInComponent (d.externalComponent 0) leg :=
    (d.legInComponent_iff_vertex_mem d.externalComponentPart.2 leg).2
      (by simpa [hv] using v.2)
  let legB : {leg : Fin (2 * (2 * S.card + 1)) //
      d.legInComponent (d.externalComponent 0) leg} := ⟨leg, hleg⟩
  refine ⟨?_, d.externalBlockLegEquiv legB, ?_, ?_⟩
  · intro h
    apply hne
    have h' := congrArg (d.externalBlockVertexEquiv).symm h
    simpa using congrArg Subtype.val h'
  · rw [d.twoPointVertexOfLeg_externalBlockLegEquiv legB]
    apply congrArg d.externalBlockVertexEquiv
    apply Subtype.ext
    exact hv
  · change twoPointVertexOfLeg
      (d.restrictedExternalPairing.partner (d.externalBlockLegEquiv legB)) = _
    rw [d.restrictedExternalPairing_partner_externalBlockLegEquiv legB]
    let partnerB := d.restrictedPartner (d.externalComponent 0) legB
    have htransport := d.twoPointVertexOfLeg_externalBlockLegEquiv partnerB
    refine htransport.trans ?_
    apply congrArg d.externalBlockVertexEquiv
    apply Subtype.ext
    change twoPointVertexOfLeg (d.pairing.partner leg) = w.1
    simpa [partnerB] using hw

private theorem TwoPointDiagram.mem_externalComponent_of_reachable_right
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    {v w : TwoPointVertex S} (hw : w ∈ d.externalComponent 0)
    (hvw : d.vertexGraph.Reachable v w) : v ∈ d.externalComponent 0 := by
  have hwBlock : d.componentBlock w = d.externalComponent 0 :=
    (d.componentBlock_eq_iff_mem d.externalComponentPart.2 w).2 hw
  have hvBlock : d.componentBlock v = d.componentBlock w :=
    d.componentBlock_eq_of_reachable hvw
  exact (d.componentBlock_eq_iff_mem d.externalComponentPart.2 v).1
    (hvBlock.trans hwBlock)

private theorem TwoPointDiagram.mem_externalComponent_of_adj_right
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    {v w : TwoPointVertex S} (hw : w ∈ d.externalComponent 0)
    (hvw : d.vertexGraph.Adj v w) : v ∈ d.externalComponent 0 :=
  d.mem_externalComponent_of_reachable_right hw hvw.reachable

/-- Ambient reachability between vertices of the external component is preserved by restriction. -/
theorem TwoPointDiagram.restrictExternalComponent_reachable
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (v w : {v : TwoPointVertex S // v ∈ d.externalComponent 0})
    (hvw : d.vertexGraph.Reachable v.1 w.1) :
    d.restrictExternalComponent.vertexGraph.Reachable
      (d.externalBlockVertexEquiv v) (d.externalBlockVertexEquiv w) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hvw
  have aux : ∀ {z : TwoPointVertex S},
      Relation.ReflTransGen d.vertexGraph.Adj v.1 z →
      ∀ hz : z ∈ d.externalComponent 0,
        d.restrictExternalComponent.vertexGraph.Reachable
          (d.externalBlockVertexEquiv v)
          (d.externalBlockVertexEquiv ⟨z, hz⟩) := by
    intro z h
    induction h with
    | refl =>
        intro hz
        exact SimpleGraph.Reachable.rfl
    | @tail b c hprefix hbc ih =>
        intro hc
        have hb : b ∈ d.externalComponent 0 :=
          d.mem_externalComponent_of_adj_right hc hbc
        have hprefix' := ih hb
        have hedge := d.restrictExternalComponent_adj
          ⟨b, hb⟩ ⟨c, hc⟩ hbc
        exact hprefix'.trans hedge.reachable
  exact aux hvw w.2

/-- The restriction to the ambient external component has no vacuum component. -/
theorem TwoPointDiagram.restrictExternalComponent_hasNoVacuumComponent
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    d.restrictExternalComponent.HasNoVacuumComponent := by
  intro v
  let vS : ↥S := ⟨v.1, TwoPointDiagram.interactionPart_subset
    (d.externalComponent 0) v.2⟩
  have hvMem : (Sum.inr vS : TwoPointVertex S) ∈ d.externalComponent 0 :=
    (TwoPointDiagram.mem_interactionPart_subtype (d.externalComponent 0) vS).1 v.2
  let ext0 : {v : TwoPointVertex S // v ∈ d.externalComponent 0} :=
    ⟨Sum.inl (0 : Fin 2), d.externalVertex_mem_externalComponentPart 0⟩
  let vint : {v : TwoPointVertex S // v ∈ d.externalComponent 0} :=
    ⟨Sum.inr vS, hvMem⟩
  have hambient : d.vertexGraph.Reachable ext0.1 vint.1 :=
    ((d.mem_componentBlock (Sum.inl (0 : Fin 2)) (Sum.inr vS)).1 hvMem).symm
  have hlocal := d.restrictExternalComponent_reachable ext0 vint hambient
  refine ⟨0, ?_⟩
  simpa [ext0, vint, vS, TwoPointDiagram.externalBlockVertexEquiv] using hlocal

/-- The restricted external component is externally connected. -/
theorem TwoPointDiagram.restrictExternalComponent_isExternallyConnected
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    d.restrictExternalComponent.IsExternallyConnected :=
  (d.restrictExternalComponent.isExternallyConnected_iff_hasNoVacuumComponent).2
    d.restrictExternalComponent_hasNoVacuumComponent

end Common
end SecondQuantization
