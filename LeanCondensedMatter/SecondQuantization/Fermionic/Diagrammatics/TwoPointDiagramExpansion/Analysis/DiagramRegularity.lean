import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Semantics.Amplitude
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Factorization.MixedComponentDysonValue
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.DiagramRegularity

set_option linter.style.header false

/-!
# Regularity of two-point diagram amplitudes

The actual two-point amplitude agrees with the arbitrary-external amplitude
after transporting the fixed-leg pairing. Measurable local boundedness is
therefore inherited from the general chamber theorem.
-/

namespace SecondQuantization
namespace Fermionic

open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- The signed pointwise amplitude of one diagram is measurably locally bounded. -/
theorem FixedExternalTwoPointWickDiagram.measurableLocallyBounded_dysonFixedTimeAmplitude
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ) (τ τ' : ℝ) :
    intervalIntegral.MeasurableLocallyBounded
      (fun σ : Fin n → ℝ => d.dysonFixedTimeAmplitude ε β g τ τ' σ) := by
  let D := twoPointDiagramExternalInsertionEquiv Finset.univ d.1
  have heq : (fun σ : Fin n → ℝ => d.dysonFixedTimeAmplitude ε β g τ τ' σ) =
      fun σ : Fin n → ℝ =>
        ExternalInsertionWickDiagram.dysonFixedTimeAmplitude D ε β g
          (twoPointExternalTimes τ τ') σ := by
    funext σ
    unfold FixedExternalTwoPointWickDiagram.dysonFixedTimeAmplitude
      ExternalInsertionWickDiagram.dysonFixedTimeAmplitude
    rw [d.fixedTimeAmplitude_eq_externalInsertion]
  rw [heq]
  exact ExternalInsertionWickDiagram.measurableLocallyBounded_dysonFixedTimeAmplitude
    D ε β g (twoPointExternalTimes τ τ')

end Fermionic
end SecondQuantization
