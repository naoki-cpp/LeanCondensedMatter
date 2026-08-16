import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ComponentRestriction
import LeanCondensedMatter.Combinatorics.InvolutionCard

set_option linter.style.header false

/-!
# Automatic external connectivity for two-point diagrams

A connected component of a two-point diagram carries a perfect matching on all of its legs, so the
number of legs in that component is even. A component containing exactly one of the two one-legged
external vertices would instead have `1 + 4k` legs. This parity contradiction shows that the two
external vertices always lie in the same component.

Consequently, for this exact two-point setup, external connectedness is equivalent to the absence of
vacuum components. The predicates remain separately defined because they express different concepts
and will differ for more general external-leg families.
-/

namespace SecondQuantization
namespace Common

variable {ExternalLabel InternalLabel : Type*} {N : ℕ}

/-- The component-partition part containing external vertex `0`. -/
noncomputable def TwoPointDiagram.externalComponentPart {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    d.componentPartition.parts :=
  ⟨d.externalComponent 0, d.componentBlock_mem_componentPartition (Sum.inl 0)⟩

/-- If the two external vertices were disconnected, external vertex `1` would not lie in the
component of external vertex `0`. -/
theorem TwoPointDiagram.externalOne_not_mem_externalComponentPart {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (hExt : ¬ d.ExternalVerticesConnected) :
    (Sum.inl (1 : Fin 2) : TwoPointVertex S) ∉
      (d.externalComponentPart : Finset (TwoPointVertex S)) := by
  intro hmem
  apply hExt
  exact ((d.mem_componentBlock
    (Sum.inl (0 : Fin 2) : TwoPointVertex S)
    (Sum.inl (1 : Fin 2) : TwoPointVertex S)).1 hmem).symm

/-- Under the hypothetical separation of the two external vertices, the legs in the component of
external vertex `0` are one external leg together with four local legs for every interaction vertex
in that component. -/
noncomputable def TwoPointDiagram.disconnectedExternalLegDataEquiv {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (hExt : ¬ d.ExternalVerticesConnected) :
    {leg : TwoPointLeg S // d.unflattenedLegInComponent d.externalComponentPart leg} ≃
      Fin 1 ⊕
        (↥(TwoPointDiagram.interactionPart (d.externalComponent 0)) × Fin 4) where
  toFun leg := by
    rcases leg with ⟨leg, hleg⟩
    cases leg with
    | inl e =>
        by_cases he : e = 0
        · exact Sum.inl 0
        · have he1 : e = 1 := by omega
          subst e
          exact False.elim (d.externalOne_not_mem_externalComponentPart hExt hleg)
    | inr p =>
        exact Sum.inr
          (⟨p.1.1, (TwoPointDiagram.mem_interactionPart_subtype
            (d.externalComponent 0) p.1).2 hleg⟩, p.2)
  invFun leg := by
    cases leg with
    | inl e =>
        exact ⟨Sum.inl 0, by
          change (Sum.inl (0 : Fin 2) : TwoPointVertex S) ∈ d.externalComponent 0
          simpa [TwoPointDiagram.externalComponent] using
            d.self_mem_componentBlock
              (Sum.inl (0 : Fin 2) : TwoPointVertex S)⟩
    | inr p =>
        let v : ↥S :=
          ⟨p.1.1, TwoPointDiagram.interactionPart_subset
            (d.externalComponent 0) p.1.2⟩
        exact ⟨Sum.inr (v, p.2), by
          change (Sum.inr v : TwoPointVertex S) ∈ d.externalComponent 0
          exact (TwoPointDiagram.mem_interactionPart_subtype
            (d.externalComponent 0) v).1 p.1.2⟩
  left_inv leg := by
    rcases leg with ⟨leg, hleg⟩
    cases leg with
    | inl e =>
        fin_cases e
        · apply Subtype.ext
          rfl
        · exact False.elim (d.externalOne_not_mem_externalComponentPart hExt hleg)
    | inr p =>
        rcases p with ⟨v, l⟩
        apply Subtype.ext
        rfl
  right_inv leg := by
    cases leg with
    | inl e =>
        fin_cases e
        rfl
    | inr p =>
        rcases p with ⟨v, l⟩
        apply congrArg Sum.inr
        apply Prod.ext
        · exact Subtype.ext (by rfl)
        · rfl

/-- Flattened legs in a hypothetically isolated external component are equivalent to one external
leg plus its quartic interaction legs. -/
noncomputable def TwoPointDiagram.disconnectedExternalBlockLegEquiv {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (hExt : ¬ d.ExternalVerticesConnected) :
    {leg : Fin (2 * (2 * S.card + 1)) //
      d.legInComponent (d.externalComponent 0) leg} ≃
      Fin 1 ⊕
        (↥(TwoPointDiagram.interactionPart (d.externalComponent 0)) × Fin 4) :=
  ((twoPointLegEquiv S).subtypeEquiv fun leg =>
      d.legInComponent_iff_unflattened d.externalComponentPart leg).trans
    (d.disconnectedExternalLegDataEquiv hExt)

open Classical in
private theorem TwoPointDiagram.card_disconnectedExternalBlockLegs {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (hExt : ¬ d.ExternalVerticesConnected) :
    Fintype.card {leg : Fin (2 * (2 * S.card + 1)) //
      d.legInComponent (d.externalComponent 0) leg} =
      1 + 4 * (TwoPointDiagram.interactionPart (d.externalComponent 0)).card := by
  calc
    Fintype.card {leg : Fin (2 * (2 * S.card + 1)) //
        d.legInComponent (d.externalComponent 0) leg} =
        Fintype.card
          (Fin 1 ⊕
            (↥(TwoPointDiagram.interactionPart (d.externalComponent 0)) × Fin 4)) :=
      Fintype.card_congr (d.disconnectedExternalBlockLegEquiv hExt)
    _ = 1 + 4 * (TwoPointDiagram.interactionPart (d.externalComponent 0)).card := by
      simp [Nat.mul_comm]

/-- In every two-point diagram, the two one-legged external vertices necessarily belong to the same
connected component. -/
theorem TwoPointDiagram.externalVerticesConnected {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    d.ExternalVerticesConnected := by
  classical
  by_contra hExt
  have hpairing :
      Combinatorics.IsPairing (d.restrictedPartner (d.externalComponent 0)) := by
    change Combinatorics.IsPairing
      (d.pairing.componentPartnerSubtypePerm twoPointVertexOfLeg d.componentBlock
        d.componentBlock_eq_of_reachable (d.externalComponent 0))
    exact d.pairing.isPairing_componentPartnerSubtypePerm twoPointVertexOfLeg d.componentBlock
      d.componentBlock_eq_of_reachable (d.externalComponent 0)
  have hEven :
      Even (Fintype.card {leg : Fin (2 * (2 * S.card + 1)) //
        d.legInComponent (d.externalComponent 0) leg}) :=
    Combinatorics.even_card_of_fixedPointFreeInvolution
      (d.restrictedPartner (d.externalComponent 0)) hpairing.1 hpairing.2
  rw [d.card_disconnectedExternalBlockLegs hExt] at hEven
  obtain ⟨k, hk⟩ := hEven
  omega

/-- The two external component blocks always coincide. -/
theorem TwoPointDiagram.externalComponent_zero_eq_one {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    d.externalComponent 0 = d.externalComponent 1 := by
  change d.componentBlock (Sum.inl (0 : Fin 2)) = d.componentBlock (Sum.inl (1 : Fin 2))
  exact (d.componentBlock_eq_iff_reachable
    (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2))).2 d.externalVerticesConnected

/-- Every external vertex lies in the common external component. -/
theorem TwoPointDiagram.externalVertex_mem_externalComponentPart {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) (e : Fin 2) :
    (Sum.inl e : TwoPointVertex S) ∈
      (d.externalComponentPart : Finset (TwoPointVertex S)) := by
  fin_cases e
  · simpa [TwoPointDiagram.externalComponentPart, TwoPointDiagram.externalComponent] using
      d.self_mem_componentBlock (Sum.inl (0 : Fin 2) : TwoPointVertex S)
  · rw [show (d.externalComponentPart : Finset (TwoPointVertex S)) =
      d.externalComponent 0 by rfl, d.externalComponent_zero_eq_one]
    simpa [TwoPointDiagram.externalComponent] using
      d.self_mem_componentBlock (Sum.inl (1 : Fin 2) : TwoPointVertex S)

/-- For two one-legged external insertions and quartic interaction vertices, external connectedness
is exactly the absence of vacuum components. -/
theorem TwoPointDiagram.isExternallyConnected_iff_hasNoVacuumComponent
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    d.IsExternallyConnected ↔ d.HasNoVacuumComponent := by
  simp [TwoPointDiagram.IsExternallyConnected, d.externalVerticesConnected]

/-- Equivalent finite-component form of external connectedness. -/
theorem TwoPointDiagram.isExternallyConnected_iff_vacuumComponentParts_eq_empty
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    d.IsExternallyConnected ↔ d.vacuumComponentParts = ∅ := by
  rw [d.isExternallyConnected_iff_hasNoVacuumComponent,
    d.hasNoVacuumComponent_iff_vacuumComponentParts_eq_empty]

end Common
end SecondQuantization
