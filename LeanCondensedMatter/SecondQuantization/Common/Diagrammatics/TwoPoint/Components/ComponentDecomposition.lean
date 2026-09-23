import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.External.ExternalConnectivity

set_option linter.style.header false

/-!
# External/vacuum decomposition of two-point components

For the direct two-point diagram model, the two distinguished one-legged external vertices always
lie in one common component. Consequently every component part is either that canonical external
part or a vacuum part, and these alternatives are disjoint.

This module packages that decomposition at the level of component indices and interaction vertices.
It also supplies generic finite-sum and finite-product splittings that later amplitude-factorization
proofs can instantiate with component-local weights.
-/

namespace SecondQuantization
namespace Common

variable {ExternalLabel InternalLabel : Type*} {N : ℕ}

/-- The interaction slots carried by the canonical external component. -/
noncomputable def TwoPointDiagram.externalInteractionPart
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S) : Finset (Fin N) :=
  interactionSector (d.vertexGraph.componentBlock (Sum.inl 0))

/-- A component part is vacuum exactly when it differs from the canonical external part. -/
@[simp]
theorem TwoPointDiagram.componentIsVacuum_iff_ne_externalComponentPart
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : d.vertexGraph.componentPartition.parts) :
    ComponentIsVacuum (B : Finset (TwoPointVertex S)) ↔
      B ≠ d.externalComponentPart := by
  unfold ComponentIsVacuum
  constructor
  · intro hVac hEq
    apply hVac
    rw [hEq]
    exact ⟨0, d.externalVertex_mem_externalComponentPart 0⟩
  · intro hNe hMeet
    obtain ⟨e, hEq⟩ := (componentMeetsExternal_iff_exists_eq_componentBlock d.vertexGraph B).1 hMeet
    apply hNe
    apply Subtype.ext
    fin_cases e
    · exact hEq
    · exact hEq.trans d.externalComponent_zero_eq_one.symm

/-- A commutative product over all component parts splits into the external part and all vacuum
parts. -/
theorem TwoPointDiagram.prod_componentParts_eq_external_mul_prod_vacuum
    {M : Type*} [CommMonoid M]
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (f : d.vertexGraph.componentPartition.parts → M) :
    (∏ B : d.vertexGraph.componentPartition.parts, f B) =
      f d.externalComponentPart * (vacuumComponentParts d.vertexGraph).prod f := by
  classical
  have hparts :
      (Finset.univ : Finset d.vertexGraph.componentPartition.parts) =
        insert d.externalComponentPart (vacuumComponentParts d.vertexGraph) := by
    ext B
    simp only [Finset.mem_univ, true_iff, Finset.mem_insert]
    by_cases hB : B = d.externalComponentPart
    · exact Or.inl hB
    · exact Or.inr ((mem_vacuumComponentParts d.vertexGraph B).2
        ((d.componentIsVacuum_iff_ne_externalComponentPart B).2 hB))
  have hExternal :
      d.externalComponentPart ∉ vacuumComponentParts d.vertexGraph := by
    rw [mem_vacuumComponentParts,
      d.componentIsVacuum_iff_ne_externalComponentPart]
    simp
  change (Finset.univ : Finset d.vertexGraph.componentPartition.parts).prod f = _
  rw [hparts, Finset.prod_insert hExternal]

/-- A fixed interaction vertex cannot belong to two distinct component interaction parts. -/
theorem TwoPointDiagram.interactionSector_component_unique
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (v : ↥S) (B C : d.vertexGraph.componentPartition.parts)
    (hvB : (v : Fin N) ∈ interactionSector
      (B : Finset (TwoPointVertex S)))
    (hvC : (v : Fin N) ∈ interactionSector
      (C : Finset (TwoPointVertex S))) :
    B = C := by
  apply Subtype.ext
  have hBgraph : (B : Finset (TwoPointVertex S)) ∈ d.vertexGraph.componentPartition.parts := B.2
  have hCgraph : (C : Finset (TwoPointVertex S)) ∈ d.vertexGraph.componentPartition.parts := C.2
  have hB : d.vertexGraph.componentBlock (Sum.inr v) = (B : Finset (TwoPointVertex S)) :=
    (d.vertexGraph.componentBlock_eq_iff_mem hBgraph (Sum.inr v)).2
      ((mem_interactionSector_subtype
        (B : Finset (TwoPointVertex S)) v).1 hvB)
  have hC : d.vertexGraph.componentBlock (Sum.inr v) = (C : Finset (TwoPointVertex S)) :=
    (d.vertexGraph.componentBlock_eq_iff_mem hCgraph (Sum.inr v)).2
      ((mem_interactionSector_subtype
        (C : Finset (TwoPointVertex S)) v).1 hvC)
  exact hB.symm.trans hC

end Common
end SecondQuantization
