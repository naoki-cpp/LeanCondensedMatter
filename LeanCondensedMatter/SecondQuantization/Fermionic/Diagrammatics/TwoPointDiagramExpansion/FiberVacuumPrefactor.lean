import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.FiberDecomposition
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentDysonValue
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.Amplitude
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.SlotSplitVacuumVertexProduct

set_option linter.style.header false

/-!
# Vacuum Dyson prefactor of a fixed external-slot fiber

The Common slot-split bridge reassembles the vacuum-component Dyson signs and arbitrary vertex-local
weights.  Specializing the latter to the quartic coupling identifies the complete statistics-free
vacuum prefactor appearing in the two-point component factorization with the standalone quartic
vacuum diagram prefactor.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode] {n : ℕ} {i j : Mode}

/-- Reassemble a fixed-external two-point diagram from a chosen external piece and quartic vacuum
piece. -/
noncomputable def fixedExternalOfSlotSplit (T : Finset (Fin n))
    (ext : FixedExternalTwoPointWickDiagramOn Mode n T i j)
    (vac : QuarticWickDiagram Mode n ((Finset.univ : Finset (Fin n)) \ T)) :
    FixedExternalTwoPointWickDiagram Mode n i j :=
  ⟨Common.TwoPointDiagram.ofSlotSplit (Finset.subset_univ T) ext.1 vac, ext.2⟩

/-- For an externally connected left piece, the product of the ambient vacuum-component Dyson signs
and coupling weights is exactly the Dyson sign and coupling weight of the standalone quartic vacuum
piece. -/
theorem fixedExternalOfSlotSplit_prod_vacuumDysonSign_mul_vertexWeight
    (g : QuarticVertexLabel Mode → ℂ) (T : Finset (Fin n))
    (ext : FixedExternalTwoPointWickDiagramOn Mode n T i j)
    (hext : ext.1.IsExternallyConnected)
    (vac : QuarticWickDiagram Mode n ((Finset.univ : Finset (Fin n)) \ T)) :
    let d := fixedExternalOfSlotSplit T ext vac
    d.1.vacuumComponentParts.prod (fun B =>
      d.mixedComponentDysonSign B * d.mixedComponentVertexWeight g B) =
      (-1 : ℂ) ^ ((Finset.univ : Finset (Fin n)) \ T).card * vac.couplingWeight g := by
  classical
  let d := fixedExternalOfSlotSplit T ext vac
  change d.1.vacuumComponentParts.prod (fun B =>
      d.mixedComponentDysonSign B * d.mixedComponentVertexWeight g B) = _
  rw [Finset.prod_mul_distrib]
  have hsign : d.1.vacuumComponentParts.prod d.mixedComponentDysonSign =
      (-1 : ℂ) ^ ((Finset.univ : Finset (Fin n)) \ T).card := by
    simpa [d, fixedExternalOfSlotSplit,
      FixedExternalTwoPointWickDiagram.mixedComponentDysonSign] using
      (Common.TwoPointDiagram.prod_slotSplitVacuumComponentSigns_eq
        (Finset.subset_univ T) ext.1 vac hext)
  have hvertex : d.1.vacuumComponentParts.prod (d.mixedComponentVertexWeight g) =
      vac.couplingWeight g := by
    simpa [d, fixedExternalOfSlotSplit,
      FixedExternalTwoPointWickDiagram.mixedComponentVertexWeight,
      QuarticWickDiagram.couplingWeight] using
      (Common.TwoPointDiagram.prod_slotSplitVacuumComponents_eq_vacuumVertexProduct
        (Finset.subset_univ T) ext.1 vac hext g)
  rw [hsign, hvertex]

end Fermionic
end SecondQuantization
