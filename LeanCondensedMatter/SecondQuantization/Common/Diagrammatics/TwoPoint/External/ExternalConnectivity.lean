import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Components.ComponentRestriction
import LeanCondensedMatter.Combinatorics.PerfectPairing.InvolutionCard

set_option linter.style.header false

/-!
# Automatic external connectivity for two-point diagrams

A connected component of a two-point diagram carries a perfect matching on all of its legs, so the
number of legs in that component is even. A component containing exactly one of the two one-legged
external vertices would instead have `1 + 4k` legs. This parity contradiction shows that the two
external vertices always lie in the same component.

Consequently, for this exact two-point setup, external connectedness is equivalent to the absence of
vacuum components. The TwoPoint-specific predicate remains `IsExternallyConnected`; vacuum-freeness is the generic
external/internal graph predicate `HasNoVacuumComponent`.
-/

namespace SecondQuantization
namespace Common

variable {ExternalLabel InternalLabel : Type*} {N : ℕ}

/-- The component-partition part containing external vertex `0`. -/
noncomputable def TwoPointDiagram.externalComponentPart {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    d.vertexGraph.componentPartition.parts :=
  ⟨d.vertexGraph.componentBlock (Sum.inl 0),
    d.vertexGraph.componentBlock_mem_componentPartition (Sum.inl 0)⟩

/-- In every two-point diagram the two external vertices belong to the same component,
because every component has an even number of one-legged external vertices. -/
theorem TwoPointDiagram.externalVerticesConnected {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    d.ExternalVerticesConnected := by
  classical
  apply SimpleGraph.reachable_finTwo_of_even_left_components d.vertexGraph
  intro B
  let blockEquiv :
      {leg : Fin (2 * (2 * S.card + 1)) //
        d.legInComponent (B : Finset (TwoPointVertex S)) leg} ≃
        ↥(Finset.toLeft (B : Finset (TwoPointVertex S))) ⊕
          (↥(interactionSector (B : Finset (TwoPointVertex S))) × Fin 4) :=
    ((twoPointLegEquiv S).subtypeEquiv fun leg =>
        d.legInComponent_iff_unflattened B leg).trans
      (componentLegDataEquiv
        (External := Fin 2) (Vertex := Fin N) (Local := Fin 4)
        (B : Finset (TwoPointVertex S)))
  simpa only [Fintype.card_coe] using
    d.pairing.even_card_left_of_invariant_subtype
      (d.legInComponent (B : Finset (TwoPointVertex S)))
      (fun leg => d.legInComponent_partner_iff
        (B : Finset (TwoPointVertex S)) leg)
      blockEquiv
      (by simpa only [Fintype.card_fin] using (show Even 4 from ⟨2, rfl⟩))

/-- The two external component blocks always coincide. -/
theorem TwoPointDiagram.externalComponent_zero_eq_one {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    d.vertexGraph.componentBlock (Sum.inl 0) = d.vertexGraph.componentBlock (Sum.inl 1) :=
  (d.vertexGraph.componentBlock_eq_iff_reachable
    (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2))).2 d.externalVerticesConnected

/-- Every external vertex lies in the common external component. -/
theorem TwoPointDiagram.externalVertex_mem_externalComponentPart {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) (e : Fin 2) :
    (Sum.inl e : TwoPointVertex S) ∈
      (d.externalComponentPart : Finset (TwoPointVertex S)) := by
  fin_cases e
  · change (Sum.inl (0 : Fin 2) : TwoPointVertex S) ∈
      d.vertexGraph.componentBlock (Sum.inl 0)
    exact d.vertexGraph.self_mem_componentBlock (Sum.inl 0)
  · rw [show (d.externalComponentPart : Finset (TwoPointVertex S)) =
      d.vertexGraph.componentBlock (Sum.inl 0) by rfl, d.externalComponent_zero_eq_one]
    change (Sum.inl (1 : Fin 2) : TwoPointVertex S) ∈
      d.vertexGraph.componentBlock (Sum.inl 1)
    exact d.vertexGraph.self_mem_componentBlock (Sum.inl 1)

/-- For two one-legged external insertions and quartic interaction vertices, external connectedness
is exactly the absence of vacuum components. -/
theorem TwoPointDiagram.isExternallyConnected_iff_hasNoVacuumComponent
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    d.IsExternallyConnected ↔ HasNoVacuumComponent d.vertexGraph := by
  simp [TwoPointDiagram.IsExternallyConnected, d.externalVerticesConnected]

/-- For two one-legged external vertices, externally connected means the entire vertex graph
is preconnected: the parity argument connects the external vertices, and vacuum-freeness
places every interaction vertex in that same component. -/
theorem TwoPointDiagram.preconnected_iff_isExternallyConnected
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    d.vertexGraph.Preconnected ↔ d.IsExternallyConnected := by
  constructor
  · intro h
    exact ⟨hasNoVacuumComponent_of_preconnected d.vertexGraph h, h _ _⟩
  · intro h
    apply (preconnected_iff_hasNoVacuumComponent_and_allExternalVerticesConnected
      d.vertexGraph).2
    refine ⟨h.1, ?_⟩
    intro a b
    fin_cases a <;> fin_cases b
    · exact SimpleGraph.Reachable.refl _
    · exact d.externalVerticesConnected
    · exact d.externalVerticesConnected.symm
    · exact SimpleGraph.Reachable.refl _

end Common
end SecondQuantization
