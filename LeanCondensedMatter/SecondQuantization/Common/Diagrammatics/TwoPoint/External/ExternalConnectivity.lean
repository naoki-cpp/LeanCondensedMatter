import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Components.ComponentRestriction
import LeanCondensedMatter.Combinatorics.InvolutionCard

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

/-- If the two external vertices were disconnected, external vertex `1` would not lie in the
component of external vertex `0`. -/
private theorem TwoPointDiagram.externalOne_not_mem_externalComponentPart {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (hExt : ¬ d.ExternalVerticesConnected) :
    (Sum.inl (1 : Fin 2) : TwoPointVertex S) ∉
      (d.externalComponentPart : Finset (TwoPointVertex S)) := by
  intro hmem
  apply hExt
  change d.vertexGraph.Reachable
    (Sum.inl (0 : Fin 2) : TwoPointVertex S)
    (Sum.inl (1 : Fin 2) : TwoPointVertex S)
  exact ((d.vertexGraph.mem_componentBlock
    (Sum.inl (0 : Fin 2) : TwoPointVertex S)
    (Sum.inl (1 : Fin 2) : TwoPointVertex S)).1 hmem).symm

/-- In every two-point diagram, the two one-legged external vertices necessarily belong to the same
connected component. -/
theorem TwoPointDiagram.externalVerticesConnected {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    d.ExternalVerticesConnected := by
  classical
  by_contra hExt
  have hExternalSector :
      Finset.toLeft (d.vertexGraph.componentBlock (Sum.inl 0)) = {0} := by
    ext e
    fin_cases e
    · simp [Finset.mem_toLeft, d.vertexGraph.self_mem_componentBlock]
    · simp only [Finset.mem_toLeft, Finset.mem_singleton]
      constructor
      · exact fun h => False.elim (d.externalOne_not_mem_externalComponentPart hExt h)
      · simp
  let blockEquiv :
      {leg : Fin (2 * (2 * S.card + 1)) //
        d.legInComponent (d.vertexGraph.componentBlock (Sum.inl 0)) leg} ≃
        ↥(Finset.toLeft (d.vertexGraph.componentBlock (Sum.inl 0))) ⊕
          (↥(interactionSector (d.vertexGraph.componentBlock (Sum.inl 0))) × Fin 4) :=
    ((twoPointLegEquiv S).subtypeEquiv fun leg =>
        d.legInComponent_iff_unflattened d.externalComponentPart leg).trans
      (componentLegDataEquiv
        (External := Fin 2) (Vertex := Fin N) (Local := Fin 4)
        (d.vertexGraph.componentBlock (Sum.inl 0)))
  let restricted :=
    d.pairing.restrict (d.legInComponent (d.vertexGraph.componentBlock (Sum.inl 0)))
      (fun leg => d.legInComponent_partner_iff (d.vertexGraph.componentBlock (Sum.inl 0)) leg)
  have hEven :
      Even (Finset.toLeft (d.vertexGraph.componentBlock (Sum.inl 0))).card := by
    simpa only [Fintype.card_coe] using
      externalCardEven_of_equiv_sum_prod blockEquiv restricted.even_card (by simpa only [Fintype.card_fin] using (show Even 4 from ⟨2, rfl⟩))
  rw [hExternalSector] at hEven
  simp at hEven

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


end Common
end SecondQuantization
