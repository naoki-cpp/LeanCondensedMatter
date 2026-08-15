import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.DysonSeries
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.ComponentAmplitudeFactorization
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.SlotSplitConnectivity

set_option linter.style.header false

/-!
# The connected perturbative two-point series

Summing only the externally connected diagrams at each order gives the connected two-point series.
The linked-cluster theorem says that this series is the vacuum-normalized one — the vacuum factors
that `ComponentAmplitudeFactorization` splits off are exactly what the division by the partition
series removes.

Connectedness is the ambient `TwoPointDiagram.IsExternallyConnected`. The Common two-point layer
owns its slot characterization, while this Fermionic module only specializes those structural facts
to the physical connected-series coefficients and amplitudes.

This module owns the connected series itself; generic connectivity structure is Common-owned.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode] {n : ℕ} {i j : Mode}

/-- **On a connected diagram the shuffle-orbit sum is a single ordered-simplex integral.** There is
no vacuum factor left: the external component owns everything. -/
theorem FixedExternalTwoPointWickDiagram.sum_componentShuffleDysonAmplitude_of_connected
    (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 ≤ β) (g : QuarticVertexLabel Mode → ℂ) (τ τ' : ℝ)
    (hconn : d.1.IsExternallyConnected) :
    (∑ shuffle : d.1.ComponentInteractionShuffle,
        (d.relabelForComponentShuffle shuffle).dysonAmplitude ε β g τ τ') =
      twoPointExternalOrderSign τ τ' *
        intervalIntegral.orderedSimplexIntegral
          (d.1.interactionComponentSize d.1.externalComponentPart) β
          (d.mixedComponentDysonLocalIntegrand ε β g τ τ'
            d.1.canonicalComponentInteractionShuffle d.1.externalComponentPart) := by
  rw [d.sum_componentShuffleDysonAmplitude_eq_external_mul_prod_vacuum ε β hβ g τ τ',
    (Common.TwoPointDiagram.isExternallyConnected_iff_vacuumComponentParts_eq_empty d.1).1 hconn,
    Finset.prod_empty, mul_one]

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

open Classical in
/-- Hence the order-zero connected coefficient is the whole order-zero diagram sum: the free
two-point function has no vacuum part to remove. -/
theorem connectedTwoPointDysonCoefficient_zero (ε : Mode → ℝ) (β : ℝ)
    (g : QuarticVertexLabel Mode → ℂ) (i j : Mode) (τ τ' : ℝ) :
    connectedTwoPointDysonCoefficient ε β g i j τ τ' 0 =
      ∑ d : FixedExternalTwoPointWickDiagram Mode 0 i j, d.dysonAmplitude ε β g τ τ' := by
  rw [connectedTwoPointDysonCoefficient,
    Finset.filter_true_of_mem fun d _ => by
      rw [d.1.isExternallyConnected_iff_externalInteractionPart_eq]
      apply Finset.eq_univ_of_forall
      intro x
      exact x.elim0]

end Fermionic
end SecondQuantization
