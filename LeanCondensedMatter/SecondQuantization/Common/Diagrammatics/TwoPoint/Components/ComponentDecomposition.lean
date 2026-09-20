import LeanCondensedMatter.Combinatorics.FinpartitionProduct
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

/-- Interaction vertices are the dependent disjoint union of the interaction parts of all full
components. -/
noncomputable def TwoPointDiagram.interactionVertexComponentEquiv
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    ↥S ≃ Σ B : d.componentPartition.parts,
      ↥(TwoPointDiagram.interactionPart (B : Finset (TwoPointVertex S))) :=
  d.componentPartition.equivSigmaSubfinsets S
    (fun v => (Sum.inr v : TwoPointVertex S))
    (fun _ => Finset.mem_univ _)
    (fun B => TwoPointDiagram.interactionPart (B : Finset (TwoPointVertex S)))
    (fun B => TwoPointDiagram.interactionPart_subset (B : Finset (TwoPointVertex S)))
    (fun B v => TwoPointDiagram.mem_interactionPart_subtype
      (B : Finset (TwoPointVertex S)) v)

@[simp]
theorem TwoPointDiagram.interactionVertexComponentEquiv_symm_val
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (x : Σ B : d.componentPartition.parts,
      ↥(TwoPointDiagram.interactionPart (B : Finset (TwoPointVertex S)))) :
    ((d.interactionVertexComponentEquiv.symm x : ↥S) : Fin N) = (x.2 : Fin N) :=
  rfl

/-- The interaction slots carried by the canonical external component. -/
noncomputable def TwoPointDiagram.externalInteractionPart
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S) : Finset (Fin N) :=
  TwoPointDiagram.interactionPart (d.externalComponent 0)

/-- A component part meets the external sector exactly when it is the canonical common external
component part. -/
private theorem TwoPointDiagram.componentMeetsExternal_iff_eq_externalComponentPart
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : d.componentPartition.parts) :
    d.ComponentMeetsExternal B ↔ B = d.externalComponentPart := by
  constructor
  · intro hB
    obtain ⟨e, hEq⟩ := (d.componentMeetsExternal_iff_eq_externalComponent B).1 hB
    apply Subtype.ext
    fin_cases e
    · exact hEq
    · exact hEq.trans d.externalComponent_zero_eq_one.symm
  · intro hB
    rw [hB]
    exact ⟨0, d.externalVertex_mem_externalComponentPart 0⟩

/-- A component part is vacuum exactly when it differs from the canonical external part. -/
@[simp]
theorem TwoPointDiagram.componentIsVacuum_iff_ne_externalComponentPart
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : d.componentPartition.parts) :
    d.ComponentIsVacuum B ↔ B ≠ d.externalComponentPart := by
  unfold TwoPointDiagram.ComponentIsVacuum
  rw [d.componentMeetsExternal_iff_eq_externalComponentPart B]

/-- The canonical external component is not a vacuum component. -/
private theorem TwoPointDiagram.externalComponentPart_not_mem_vacuumComponentParts
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    d.externalComponentPart ∉ d.vacuumComponentParts := by
  rw [d.mem_vacuumComponentParts,
    d.componentIsVacuum_iff_ne_externalComponentPart]
  simp

/-- Every component part is either the common external part or a vacuum part. -/
private theorem TwoPointDiagram.componentPart_eq_externalComponentPart_or_mem_vacuumComponentParts
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : d.componentPartition.parts) :
    B = d.externalComponentPart ∨ B ∈ d.vacuumComponentParts := by
  by_cases hB : B = d.externalComponentPart
  · exact Or.inl hB
  · exact Or.inr ((d.mem_vacuumComponentParts B).2
      ((d.componentIsVacuum_iff_ne_externalComponentPart B).2 hB))

/-- The full finite type of component parts is the disjoint insertion of the common external part
into the finite set of vacuum parts. -/
private theorem TwoPointDiagram.univ_componentParts_eq_insert_external_vacuum
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    (Finset.univ : Finset d.componentPartition.parts) =
      insert d.externalComponentPart d.vacuumComponentParts := by
  ext B
  simp only [Finset.mem_univ, true_iff, Finset.mem_insert]
  exact d.componentPart_eq_externalComponentPart_or_mem_vacuumComponentParts B

/-- A commutative product over all component parts splits into the external part and all vacuum
parts. -/
theorem TwoPointDiagram.prod_componentParts_eq_external_mul_prod_vacuum
    {M : Type*} [CommMonoid M]
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (f : d.componentPartition.parts → M) :
    (∏ B : d.componentPartition.parts, f B) =
      f d.externalComponentPart * d.vacuumComponentParts.prod f := by
  classical
  change (Finset.univ : Finset d.componentPartition.parts).prod f = _
  rw [d.univ_componentParts_eq_insert_external_vacuum,
    Finset.prod_insert d.externalComponentPart_not_mem_vacuumComponentParts]

/-- A fixed interaction vertex cannot belong to two distinct component interaction parts. -/
theorem TwoPointDiagram.interactionPart_component_unique
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (v : ↥S) (B C : d.componentPartition.parts)
    (hvB : (v : Fin N) ∈ TwoPointDiagram.interactionPart
      (B : Finset (TwoPointVertex S)))
    (hvC : (v : Fin N) ∈ TwoPointDiagram.interactionPart
      (C : Finset (TwoPointVertex S))) :
    B = C := by
  apply Subtype.ext
  have hBgraph : (B : Finset (TwoPointVertex S)) ∈ d.vertexGraph.componentPartition.parts := by
    simpa only [TwoPointDiagram.componentPartition] using B.2
  have hCgraph : (C : Finset (TwoPointVertex S)) ∈ d.vertexGraph.componentPartition.parts := by
    simpa only [TwoPointDiagram.componentPartition] using C.2
  have hB : d.vertexGraph.componentBlock (Sum.inr v) = (B : Finset (TwoPointVertex S)) :=
    (d.vertexGraph.componentBlock_eq_iff_mem hBgraph (Sum.inr v)).2
      ((TwoPointDiagram.mem_interactionPart_subtype
        (B : Finset (TwoPointVertex S)) v).1 hvB)
  have hC : d.vertexGraph.componentBlock (Sum.inr v) = (C : Finset (TwoPointVertex S)) :=
    (d.vertexGraph.componentBlock_eq_iff_mem hCgraph (Sum.inr v)).2
      ((TwoPointDiagram.mem_interactionPart_subtype
        (C : Finset (TwoPointVertex S)) v).1 hvC)
  exact hB.symm.trans hC

end Common
end SecondQuantization
