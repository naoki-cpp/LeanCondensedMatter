import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentCrossingEven
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentPairProduct
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Amplitude

set_option linter.style.header false

/-!
# Component-local mixed-time pairing values

Common owns mixed component pair fibers, crossing counts, and statistics weights. This module combines
the fermionic component weight with canonical free Gibbs contraction products and feeds that physical
component value into the fixed-time amplitude.
-/

namespace SecondQuantization
namespace Fermionic

open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- Fermionic crossing weight times the contraction product internal to one full component. -/
noncomputable def FixedExternalTwoPointWickDiagram.mixedComponentPairingValue
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (B : d.1.componentPartition.parts) : ℂ :=
  d.1.mixedComponentWeight Common.Statistics.fermion τ τ' σ B *
    ∏ pr : d.1.MixedComponentPair τ τ' σ B,
      d.mixedPairContractionValue ε β τ τ' σ pr.1

end Fermionic
end SecondQuantization
