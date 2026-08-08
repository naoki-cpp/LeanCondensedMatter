import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ExternalRestriction

set_option linter.style.header false

/-!
# Connectedness of the restricted external component

Restriction to the component containing the distinguished external vertices preserves its complete
pairing graph.  Hence the restricted two-point diagram has no vacuum component (and therefore is
externally connected in the two-one-legged-external setup).
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
    | inr w => exact Sum.inr
        ⟨w.1, (TwoPointDiagram.mem_interactionPart_subtype
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
    · apply Subtype.ext; rfl
    · apply Subtype.ext; rfl
  right_inv v := by
    rcases v with e | w
    · rfl
    · apply congrArg Sum.inr
      exact Subtype.ext (by rfl)

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
    (d.legInComponent_iff_vertex_mem d.externalComponentPart leg).2 (by simpa [hv] using v.2)
  let legB : {leg : Fin (2 * (2 * S.card + 1)) //
      d.legInComponent (d.externalComponent 0) leg} := ⟨leg, hleg⟩
  refine ⟨?_, d.externalBlockLegEquiv legB, ?_, ?_⟩
  · intro h
    apply hne
    have := congrArg (d.externalBlockVertexEquiv).symm h
    simpa using congrArg Subtype.val this
  · apply (d.externalBlockVertexEquiv).injective
    apply Subtype.ext
    change twoPointVertexOfLeg leg = v.1
    exact hv
  · apply (d.externalBlockVertexEquiv).injective
    apply Subtype.ext
    change twoPointVertexOfLeg (d.pairing.partner leg) = w.1
    rw [← d.restrictedPartner_val (d.externalComponent 0) legB]
    have hpair := d.restrictedExternalPairing_partner_externalBlockLegEquiv legB
    rw [← hpair]
    change twoPointVertexOfLeg (d.pairing.partner leg) = w.1
    exact hw

private theorem TwoPointDiagram.mem_externalComponent_of_adj_right
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    {v w : TwoPointVertex S} (hw : w ∈ d.externalComponent 0)
    (hvw : d.vertexGraph.Adj v w) : v ∈ d.externalComponent 0 := by
  have hwBlock : d.componentBlock w = d.externalComponent 0 :=
    (d.componentBlock_eq_iff_mem d.externalComponentPart.2 w).2 hw
  have hvwReach : d.vertexGraph.Reachable v w := hvw.reachable
  have hvBlock : d.componentBlock v = d.componentBlock w :=
    d.componentBlock_eq_of_reachable hvwReach
  exact (d.componentBlock_eq_iff_mem d.externalComponentPart.2 v).1
    (hvBlock.trans hwBlock)

/-- Ambient reachability between vertices of the external component is preserved by restriction. -/
theorem TwoPointDiagram.restrictExternalComponent_reachable
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (v w : {v : TwoPointVertex S // v ∈ d.externalComponent 0})
    (hvw : d.vertexGraph.Reachable v.1 w.1) :
    d.restrictExternalComponent.vertexGraph.Reachable
      (d.externalBlockVertexEquiv v) (d.externalBlockVertexEquiv w) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hvw ⊢
  induction hvw generalizing w with
  | refl => exact Relation.ReflTransGen.refl
  | @tail x y z hxy hyz ih =>
      have hyMem : y ∈ d.externalComponent 0 :=
        d.mem_externalComponent_of_adj_right w.2 hyz
      let yB : {v : TwoPointVertex S // v ∈ d.externalComponent 0} := ⟨y, hyMem⟩
      have hprefix := ih yB
      have hedge := d.restrictExternalComponent_adj yB w hyz
      exact Relation.ReflTransGen.tail hprefix hedge

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
  simpa [ext0, vint, TwoPointDiagram.externalBlockVertexEquiv] using hlocal

/-- The restricted external component is externally connected. -/
theorem TwoPointDiagram.restrictExternalComponent_isExternallyConnected
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    d.restrictExternalComponent.IsExternallyConnected :=
  (d.restrictExternalComponent.isExternallyConnected_iff_hasNoVacuumComponent).2
    d.restrictExternalComponent_hasNoVacuumComponent

end Common
end SecondQuantization
