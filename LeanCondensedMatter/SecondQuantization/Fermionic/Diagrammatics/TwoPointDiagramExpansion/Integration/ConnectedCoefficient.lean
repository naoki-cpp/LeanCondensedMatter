import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Integration.DysonCoefficient

set_option linter.style.header false

/-!
# Connected two-point Dyson coefficient

This module owns the coefficient-level connected two-point endpoint.  It belongs to the integration
layer because each summand is an integrated Dyson amplitude.  Formal power-series packaging remains
in `Series/DysonSeries.lean`.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

open Classical in
/-- The order-`n` coefficient of the connected two-point series: the integrated Dyson amplitudes of
the externally connected diagrams only. -/
noncomputable def connectedTwoPointDysonCoefficient (ε : Mode → ℝ) (β : ℝ)
    (g : QuarticVertexLabel Mode → ℂ) (i j : Mode) (τ τ' : ℝ) (n : ℕ) : ℂ :=
  ∑ d ∈ (Finset.univ : Finset (FixedExternalTwoPointWickDiagram Mode n i j)).filter
      fun d => d.1.IsExternallyConnected,
    d.dysonAmplitude ε β g τ τ'

end Fermionic
end SecondQuantization
