import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.SlotSplit.ExternalSupportConnectivity

set_option linter.style.header false

/-!
# Fibers of the external-support decomposition

Fixing the ambient interaction slots `S` and the externally supported subset `T`, the diagrams
with support exactly `T` are equivalent to a vacuum-free external-insertion diagram on `T`
together with an arbitrary quartic diagram on the complement `S \\ T`.

Unlike a fully connected cumulant, the external-bearing diagram may have multiple disconnected
components meeting different external insertions.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*} {E N : ℕ}
  {S T : Finset (Fin N)}

private theorem ExternalInsertionDiagram.pairing_isSplit_of_support_eq
    (h : T ⊆ S)
    {d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S}
    (hd : d.externallySupportedInteractionPart = T) :
    d.pairing.IsSplit (externalInsertionSlotLegSplitting (E := E) h) := by
  subst hd
  exact d.pairing_isSplit_externallySupportedInteractionPart

private theorem ExternalInsertionDiagram.hasNoVacuumComponent_slotSplitExternal_of_support_eq
    (h : T ⊆ S)
    {d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S}
    (hd : d.externallySupportedInteractionPart = T)
    (hsplit : d.pairing.IsSplit (externalInsertionSlotLegSplitting (E := E) h)) :
    HasNoVacuumComponent (d.slotSplitExternal h hsplit).vertexGraph := by
  subst hd
  simpa [ExternalInsertionDiagram.externalSupportDiagram] using
    d.hasNoVacuumComponent_externalSupportDiagram

/-- Fiber over a chosen externally supported interaction-slot subset.

The inverse assembles the two diagrams without joining their pairings. Vacuum-freeness of the
external piece ensures that no supported slot is lost upon reassembly. -/
noncomputable def ExternalInsertionDiagram.externalSupportFiberEquiv
    (h : T ⊆ S) :
    {d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S //
      d.externallySupportedInteractionPart = T} ≃
      {ext : ExternalInsertionDiagram ExternalLabel InternalLabel E N T //
        HasNoVacuumComponent ext.vertexGraph} ×
        QuarticDiagram InternalLabel N (S \\ T) where
  toFun d :=
    (⟨d.1.slotSplitExternal h
        (ExternalInsertionDiagram.pairing_isSplit_of_support_eq h d.2),
      ExternalInsertionDiagram.hasNoVacuumComponent_slotSplitExternal_of_support_eq
        h d.2 _⟩,
      d.1.slotSplitVacuum h
        (ExternalInsertionDiagram.pairing_isSplit_of_support_eq h d.2))
  invFun p :=
    ⟨ExternalInsertionDiagram.ofSlotSplit h p.1.1 p.2,
      ExternalInsertionDiagram.externallySupportedInteractionPart_ofSlotSplit
        h p.1.1 p.2 p.1.2⟩
  left_inv d :=
    Subtype.ext (ExternalInsertionDiagram.ofSlotSplit_slotSplit h d.1
      (ExternalInsertionDiagram.pairing_isSplit_of_support_eq h d.2))
  right_inv p := by
    obtain ⟨⟨ext, hext⟩, vac⟩ := p
    simp only [Prod.mk.injEq]
    refine ⟨Subtype.ext ?_, ?_⟩
    · exact ExternalInsertionDiagram.slotSplitExternal_ofSlotSplit h ext vac _
    · exact ExternalInsertionDiagram.slotSplitVacuum_ofSlotSplit h ext vac _

end Common
end SecondQuantization
