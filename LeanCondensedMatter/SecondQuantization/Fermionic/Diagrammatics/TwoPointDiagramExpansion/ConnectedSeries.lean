import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.DysonSeries
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedExternalPositions

set_option linter.style.header false

/-!
# The connected perturbative two-point series

A fixed-external two-point diagram is connected exactly when its external component owns every
interaction slot: any slot it does not own belongs to a vacuum component, and conversely a vacuum
component owns at least the slots of its own vertices.

Summing only the connected diagrams at each order gives the connected two-point series. The
linked-cluster theorem says that this series is the vacuum-normalized one — the vacuum factors that
`ComponentAmplitudeFactorization` splits off are exactly what the division by the partition series
removes.

This module owns the connected object itself; the theorem identifying it is separate.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode] {n : ℕ} {i j : Mode}

omit [LinearOrder Mode] [Fintype Mode] in
/-- The slots the external component owns are the interaction part of the external component: the
index the fiberwise diagram sum is organized by. -/
theorem FixedExternalTwoPointWickDiagram.externalSlots_eq_interactionPart
    (d : FixedExternalTwoPointWickDiagram Mode n i j) :
    d.externalSlots =
      Common.TwoPointDiagram.interactionPart (d.1.externalComponent 0) := rfl

/-- **A fixed-external diagram is connected** when its external component owns every interaction
slot, leaving no vacuum component to factor off. -/
def FixedExternalTwoPointWickDiagram.IsConnected
    (d : FixedExternalTwoPointWickDiagram Mode n i j) : Prop :=
  d.externalSlots = (Finset.univ : Finset (Fin n))

open Classical in
/-- The order-`n` coefficient of the connected two-point series: the integrated Dyson amplitudes of
the connected diagrams only. -/
noncomputable def connectedTwoPointDysonCoefficient (ε : Mode → ℝ) (β : ℝ)
    (g : QuarticVertexLabel Mode → ℂ) (i j : Mode) (τ τ' : ℝ) (n : ℕ) : ℂ :=
  ∑ d ∈ (Finset.univ : Finset (FixedExternalTwoPointWickDiagram Mode n i j)).filter
      FixedExternalTwoPointWickDiagram.IsConnected,
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

omit [LinearOrder Mode] [Fintype Mode] in
/-- At order zero there are no interaction slots, so every diagram is connected. -/
theorem isConnected_of_zero (d : FixedExternalTwoPointWickDiagram Mode 0 i j) :
    d.IsConnected := by
  apply Finset.eq_univ_of_forall
  intro x
  exact x.elim0

open Classical in
/-- Hence the order-zero connected coefficient is the whole order-zero diagram sum: the free
two-point function has no vacuum part to remove. -/
theorem connectedTwoPointDysonCoefficient_zero (ε : Mode → ℝ) (β : ℝ)
    (g : QuarticVertexLabel Mode → ℂ) (i j : Mode) (τ τ' : ℝ) :
    connectedTwoPointDysonCoefficient ε β g i j τ τ' 0 =
      ∑ d : FixedExternalTwoPointWickDiagram Mode 0 i j, d.dysonAmplitude ε β g τ τ' := by
  rw [connectedTwoPointDysonCoefficient,
    Finset.filter_true_of_mem fun d _ => isConnected_of_zero d]

end Fermionic
end SecondQuantization
