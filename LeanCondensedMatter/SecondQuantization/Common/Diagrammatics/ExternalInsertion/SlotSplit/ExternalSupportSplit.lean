import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalComponents
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.SlotSplit.SlotLegSplitting

set_option linter.style.header false

/-!
# Canonical external-support slot split

For an arbitrary external-insertion diagram, the interaction slots belonging to components that meet
the external sector form a canonical finite subset. All remaining interaction slots lie in pure
vacuum components.

The pairing cannot cross between these two sectors. This supplies the semantic split used later to
decompose a fixed-external diagram into a vacuum-free external-bearing piece and a quartic vacuum
piece.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*} {E N : ℕ}

open Classical in
/-- The interaction vertices whose connected components meet at least one external insertion. -/
noncomputable def ExternalInsertionDiagram.externallySupportedInteractionPart
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S) :
    Finset (Fin N) :=
  S.filter fun v =>
    ∃ hv : v ∈ S,
      ComponentMeetsExternal
        (d.vertexGraph.componentBlock
          (Sum.inr (⟨v, hv⟩ : ↥S)))

/-- The externally supported interaction slots are ambient interaction slots. -/
theorem ExternalInsertionDiagram.externallySupportedInteractionPart_subset
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S) :
    d.externallySupportedInteractionPart ⊆ S := by
  classical
  intro v hv
  exact (Finset.mem_filter.1 hv).1

/-- An interaction vertex belongs to the canonical external-support slot set exactly when its
connected component meets the external sector. -/
@[simp]
theorem ExternalInsertionDiagram.mem_externallySupportedInteractionPart
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (v : ↥S) :
    v.1 ∈ d.externallySupportedInteractionPart ↔
      ComponentMeetsExternal
        (d.vertexGraph.componentBlock (Sum.inr v)) := by
  classical
  constructor
  · intro hv
    obtain ⟨-, ⟨hS, hmeet⟩⟩ :=
      Finset.mem_filter.1 hv
    have hsub : (⟨v.1, hS⟩ : ↥S) = v := by
      apply Subtype.ext
      rfl
    simpa only [hsub] using hmeet
  · intro hmeet
    refine Finset.mem_filter.2 ⟨v.2, ?_⟩
    exact ⟨v.2, hmeet⟩

/-- Vacuum-freeness means precisely that every ambient interaction slot belongs to the canonical
externally supported slot set. -/
theorem ExternalInsertionDiagram.hasNoVacuumComponent_iff_externallySupportedInteractionPart_eq
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S) :
    HasNoVacuumComponent d.vertexGraph ↔
      d.externallySupportedInteractionPart = S := by
  classical
  constructor
  · intro h
    apply Finset.Subset.antisymm d.externallySupportedInteractionPart_subset
    intro v hv
    let vS : ↥S := ⟨v, hv⟩
    obtain ⟨e, he⟩ := h vS
    apply (d.mem_externallySupportedInteractionPart vS).2
    refine ⟨e, ?_⟩
    exact (d.vertexGraph.mem_componentBlock (Sum.inr vS) (Sum.inl e)).2 he
  · intro h v
    have hv :
        v.1 ∈ d.externallySupportedInteractionPart := by
      rw [h]
      exact v.2
    obtain ⟨e, he⟩ := (d.mem_externallySupportedInteractionPart v).1 hv
    refine ⟨e, ?_⟩
    exact (d.vertexGraph.mem_componentBlock (Sum.inr v) (Sum.inl e)).1 he

private theorem ExternalInsertionDiagram.exists_externalSupportLeftSlot_iff
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (leg : Fin (2 * (2 * S.card + E))) :
    (∃ i : Fin (2 * (2 * d.externallySupportedInteractionPart.card + E)),
        externalInsertionSlotLegSplitting (E := E)
            d.externallySupportedInteractionPart_subset (Sum.inl i) = leg) ↔
      ComponentMeetsExternal
        (d.vertexGraph.componentBlock
          (externalInsertionVertexOfLeg leg)) := by
  classical
  let T := d.externallySupportedInteractionPart
  let hT : T ⊆ S := d.externallySupportedInteractionPart_subset
  constructor
  · rintro ⟨i, rfl⟩
    let x := externalInsertionLegEquiv E T i
    have hi : i = (externalInsertionLegEquiv E T).symm x := by
      simp [x]
    cases hx : x with
    | inl e =>
        rw [hx] at hi
        rw [hi, externalInsertionSlotLegSplitting_external]
        change ComponentMeetsExternal
          (d.vertexGraph.componentBlock (Sum.inl e))
        exact ⟨e, d.vertexGraph.self_mem_componentBlock (Sum.inl e)⟩
    | inr p =>
        obtain ⟨v, l⟩ := p
        rw [hx] at hi
        rw [hi, externalInsertionSlotLegSplitting_left_interaction]
        let vS : ↥S := ⟨v.1, hT v.2⟩
        change ComponentMeetsExternal
          (d.vertexGraph.componentBlock (Sum.inr vS))
        exact (d.mem_externallySupportedInteractionPart vS).1 v.2
  · intro hmeet
    let x := externalInsertionLegEquiv E S leg
    cases hx : x with
    | inl e =>
        refine ⟨(externalInsertionLegEquiv E T).symm (Sum.inl e), ?_⟩
        rw [externalInsertionSlotLegSplitting_external]
        apply (externalInsertionLegEquiv E S).injective
        simpa [x] using hx.symm
    | inr p =>
        obtain ⟨v, l⟩ := p
        have hmeet' :
            ComponentMeetsExternal
              (d.vertexGraph.componentBlock (Sum.inr v)) := by
          simpa [externalInsertionVertexOfLeg, x, hx] using hmeet
        have hvT : v.1 ∈ T := by
          exact (d.mem_externallySupportedInteractionPart v).2 hmeet'
        refine
          ⟨(externalInsertionLegEquiv E T).symm
              (Sum.inr (⟨v.1, hvT⟩, l)), ?_⟩
        rw [externalInsertionSlotLegSplitting_left_interaction]
        apply (externalInsertionLegEquiv E S).injective
        simpa [x] using hx.symm

/-- The canonical divide between externally supported interaction slots and the remaining vacuum
slots is respected by the ambient pairing. -/
theorem ExternalInsertionDiagram.pairing_isSplit_externallySupportedInteractionPart
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S) :
    d.pairing.IsSplit
      (externalInsertionSlotLegSplitting (E := E)
        d.externallySupportedInteractionPart_subset) := by
  classical
  intro i
  let split :=
    externalInsertionSlotLegSplitting (E := E)
      d.externallySupportedInteractionPart_subset
  let leg := split (Sum.inl i)
  have hmeet :
      ComponentMeetsExternal
        (d.vertexGraph.componentBlock
          (externalInsertionVertexOfLeg leg)) :=
    (d.exists_externalSupportLeftSlot_iff leg).1 ⟨i, rfl⟩
  have hblock :=
    d.pairing.vertexGraph_componentBlock_partner
      (externalInsertionVertexOfLeg (E := E)) leg
  have hpartner :
      ComponentMeetsExternal
        (d.vertexGraph.componentBlock
          (externalInsertionVertexOfLeg (d.pairing.partner leg))) := by
    change ComponentMeetsExternal
      ((d.pairing.vertexGraph (externalInsertionVertexOfLeg (E := E))).componentBlock
        (externalInsertionVertexOfLeg (d.pairing.partner leg)))
    rw [← hblock]
    simpa [ExternalInsertionDiagram.vertexGraph] using hmeet
  obtain ⟨j, hj⟩ :=
    (d.exists_externalSupportLeftSlot_iff (d.pairing.partner leg)).2 hpartner
  exact ⟨j, hj.symm⟩

end Common
end SecondQuantization
