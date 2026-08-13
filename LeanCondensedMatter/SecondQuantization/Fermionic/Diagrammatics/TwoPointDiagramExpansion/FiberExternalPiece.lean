import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.FiberDecomposition
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.ExternalPieceAmplitude

set_option linter.style.header false

/-!
# The external piece of a fixed external-slot fiber

A fiber element already records that its canonical external interaction set is the chosen ambient
slot set `T`.  Under that equality, the ambient `externalPiece` is exactly the increasing-order
standardization of the left slot-split piece.  Both views now use the same Common-owned
`standardSlotEquiv`, so no parallel standardization or transport bridge is involved.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode] {n : ℕ} {i j : Mode}

omit [LinearOrder Mode] [Fintype Mode] in
/-- For a diagram in the external-slot fiber over `T`, its canonical standalone external piece is
exactly the increasing-order standardization of the left slot-split piece. -/
theorem FixedExternalTwoPointWickDiagram.externalPiece_heq_standardized_slotSplitExternal
    (T : Finset (Fin n))
    (d : {d : FixedExternalTwoPointWickDiagram Mode n i j // d.1.externalInteractionPart = T}) :
    HEq d.1.externalPiece
      (fixedExternalTwoPointWickDiagramOnEquiv T
        ⟨d.1.1.slotSplitExternal (Finset.subset_univ T)
            (Common.isSplit_slotLegSplitting_of_interactionPart_eq
              (Finset.subset_univ T) d.2),
          d.1.2⟩) := by
  obtain ⟨d, hd⟩ := d
  subst T
  apply heq_of_eq
  apply Subtype.ext
  have hsplit :
      d.1.externalVacuumSplit.1 =
        d.1.slotSplitExternal (Finset.subset_univ d.1.externalInteractionPart)
          (Common.isSplit_slotLegSplitting_of_interactionPart_eq
            (Finset.subset_univ d.1.externalInteractionPart) rfl) := by
    rfl
  have hcongr := congrArg
    (fun x => Common.TwoPointDiagram.slotCongr
      (Common.standardSlotEquiv d.1.externalInteractionPart) x) hsplit
  simpa [FixedExternalTwoPointWickDiagram.externalPiece,
    fixedExternalTwoPointWickDiagramOnEquiv] using hcongr

omit [LinearOrder Mode] [Fintype Mode] in
/-- After reindexing a fiber by `fixedExternalFiberEquiv`, the ambient standalone external piece is
the standardized connected external diagram and therefore does not depend on the vacuum diagram. -/
theorem fixedExternalFiberEquiv_symm_externalPiece_heq
    (T : Finset (Fin n))
    (p : {ext : FixedExternalTwoPointWickDiagramOn Mode n T i j //
            ext.1.IsExternallyConnected} ×
          QuarticWickDiagram Mode n ((Finset.univ : Finset (Fin n)) \ T)) :
    HEq ((fixedExternalFiberEquiv T).symm p).1.externalPiece
      ((connectedFixedExternalTwoPointWickDiagramOnEquiv T p.1).1) := by
  let d := (fixedExternalFiberEquiv T).symm p
  have hpiece :=
    FixedExternalTwoPointWickDiagram.externalPiece_heq_standardized_slotSplitExternal
      (Mode := Mode) (i := i) (j := j) T d
  have hright := (fixedExternalFiberEquiv T).apply_symm_apply p
  have hext :
      ⟨d.1.1.slotSplitExternal (Finset.subset_univ T)
          (Common.isSplit_slotLegSplitting_of_interactionPart_eq
            (Finset.subset_univ T) d.2), d.1.2⟩ = p.1.1 := by
    exact congrArg (fun q => q.1.1) hright
  rw [hext] at hpiece
  exact hpiece

end Fermionic
end SecondQuantization
