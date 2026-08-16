import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.DysonSeries

set_option linter.style.header false

/-!
# The connected perturbative two-point series

Summing only the externally connected diagrams at each order gives the connected two-point series.
The linked-cluster theorem identifies this series with the vacuum-normalized two-point series.

Connectedness is the ambient `TwoPointDiagram.IsExternallyConnected`; this module only packages the
physical connected coefficients and their formal power series.
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

/-- **The connected perturbative two-point series.** -/
noncomputable def connectedTwoPointDysonSeries (ε : Mode → ℝ) (β : ℝ)
    (g : QuarticVertexLabel Mode → ℂ) (i j : Mode) (τ τ' : ℝ) : PowerSeries ℂ :=
  PowerSeries.mk (connectedTwoPointDysonCoefficient ε β g i j τ τ')

@[simp]
theorem coeff_connectedTwoPointDysonSeries (ε : Mode → ℝ) (β : ℝ)
    (g : QuarticVertexLabel Mode → ℂ) (i j : Mode) (τ τ' : ℝ) (n : ℕ) :
    PowerSeries.coeff n (connectedTwoPointDysonSeries ε β g i j τ τ') =
      connectedTwoPointDysonCoefficient ε β g i j τ τ' n :=
  PowerSeries.coeff_mk n _

end Fermionic
end SecondQuantization
