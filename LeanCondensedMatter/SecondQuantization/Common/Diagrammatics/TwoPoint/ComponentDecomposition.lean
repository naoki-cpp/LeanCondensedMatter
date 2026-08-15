import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ExternalConnectivity

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
  TwoPointDiagram.interactionPart (d.externalComponent 0)

/-- A component part meets the external sector exactly when it is the canonical common external
component part. -/
theorem TwoPointDiagram.componentMeetsExternal_iff_eq_externalComponentPart
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
theorem TwoPointDiagram.externalComponentPart_not_mem_vacuumComponentParts
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    d.externalComponentPart ∉ d.vacuumComponentParts := by
  rw [d.mem_vacuumComponentParts,
    d.componentIsVacuum_iff_ne_externalComponentPart]
  simp

/-- Every component part is either the common external part or a vacuum part. -/
theorem TwoPointDiagram.componentPart_eq_externalComponentPart_or_mem_vacuumComponentParts
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : d.componentPartition.parts) :
    B = d.externalComponentPart ∨ B ∈ d.vacuumComponentParts := by
  by_cases hB : B = d.externalComponentPart
  · exact Or.inl hB
  · exact Or.inr ((d.mem_vacuumComponentParts B).2
      ((d.componentIsVacuum_iff_ne_externalComponentPart B).2 hB))

/-- The full finite type of component parts is the disjoint insertion of the common external part
into the finite set of vacuum parts. -/
theorem TwoPointDiagram.univ_componentParts_eq_insert_external_vacuum
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

/-- Every interaction vertex lies either in the common external component or in a vacuum component. -/
theorem TwoPointDiagram.mem_externalInteractionPart_or_exists_mem_vacuumInteractionPart
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (v : ↥S) :
    (v : Fin N) ∈ d.externalInteractionPart ∨
      ∃ B : d.componentPartition.parts,
        B ∈ d.vacuumComponentParts ∧
          (v : Fin N) ∈ TwoPointDiagram.interactionPart
            (B : Finset (TwoPointVertex S)) := by
  let B : d.componentPartition.parts :=
    ⟨d.componentBlock (Sum.inr v),
      d.componentBlock_mem_componentPartition (Sum.inr v)⟩
  have hvB : (Sum.inr v : TwoPointVertex S) ∈ (B : Finset (TwoPointVertex S)) := by
    exact d.self_mem_componentBlock (Sum.inr v)
  rcases d.componentPart_eq_externalComponentPart_or_mem_vacuumComponentParts B with hB | hB
  · left
    apply (TwoPointDiagram.mem_interactionPart_subtype (d.externalComponent 0) v).2
    rw [show (B : Finset (TwoPointVertex S)) = d.externalComponent 0 by
      exact congrArg Subtype.val hB] at hvB
    exact hvB
  · right
    refine ⟨B, hB, ?_⟩
    exact (TwoPointDiagram.mem_interactionPart_subtype
      (B : Finset (TwoPointVertex S)) v).2 hvB

/-- A two-point diagram is externally connected exactly when the canonical external component owns
all interaction slots. -/
theorem TwoPointDiagram.isExternallyConnected_iff_externalInteractionPart_eq
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    d.IsExternallyConnected ↔ d.externalInteractionPart = S := by
  rw [d.isExternallyConnected_iff_hasNoVacuumComponent,
    d.hasNoVacuumComponent_iff_forall_component_meetsExternal]
  constructor
  · intro hall
    apply Finset.Subset.antisymm
    · exact TwoPointDiagram.interactionPart_subset (d.externalComponent 0)
    · intro w hw
      rw [TwoPointDiagram.externalInteractionPart, TwoPointDiagram.mem_interactionPart]
      refine ⟨hw, ?_⟩
      obtain ⟨e, he⟩ := hall
        ⟨d.componentBlock (Sum.inr ⟨w, hw⟩), d.componentBlock_mem_componentPartition _⟩
      have hblock : d.externalComponent e = d.componentBlock (Sum.inr ⟨w, hw⟩) :=
        (d.componentBlock_eq_iff_mem
          (d.componentBlock_mem_componentPartition _) (Sum.inl e)).2 he
      have hzero : d.externalComponent e = d.externalComponent 0 := by
        fin_cases e
        · rfl
        · exact d.externalComponent_zero_eq_one.symm
      rw [← hzero, hblock]
      exact d.self_mem_componentBlock _
  · intro hconn B
    obtain ⟨v, -, hv⟩ := d.componentPartition.part_surjOn B.2
    cases v with
    | inl e => exact ⟨e, hv ▸ d.self_mem_componentBlock (Sum.inl e)⟩
    | inr w =>
        have hmem : (w : Fin N) ∈ d.externalInteractionPart := by
          rw [hconn]
          exact w.2
        rw [TwoPointDiagram.externalInteractionPart, TwoPointDiagram.mem_interactionPart] at hmem
        obtain ⟨hw, hw'⟩ := hmem
        have hvertex : (Sum.inr w : TwoPointVertex S) ∈ d.externalComponent 0 := by
          simpa using hw'
        have hB : (B : Finset (TwoPointVertex S)) = d.externalComponent 0 := by
          rw [← hv]
          exact (d.componentBlock_eq_iff_mem
            (d.componentBlock_mem_componentPartition (Sum.inl 0)) (Sum.inr w)).2 hvertex
        refine ⟨0, ?_⟩
        rw [hB]
        exact d.self_mem_componentBlock (Sum.inl 0)

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
  have hB : d.componentBlock (Sum.inr v) = (B : Finset (TwoPointVertex S)) :=
    (d.componentBlock_eq_iff_mem B.2 (Sum.inr v)).2
      ((TwoPointDiagram.mem_interactionPart_subtype
        (B : Finset (TwoPointVertex S)) v).1 hvB)
  have hC : d.componentBlock (Sum.inr v) = (C : Finset (TwoPointVertex S)) :=
    (d.componentBlock_eq_iff_mem C.2 (Sum.inr v)).2
      ((TwoPointDiagram.mem_interactionPart_subtype
        (C : Finset (TwoPointVertex S)) v).1 hvC)
  exact hB.symm.trans hC

end Common
end SecondQuantization
