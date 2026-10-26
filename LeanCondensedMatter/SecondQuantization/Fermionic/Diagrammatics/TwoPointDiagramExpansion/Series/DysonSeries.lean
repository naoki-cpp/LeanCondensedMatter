import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Integration.DysonCoefficient
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Integration.DiagramSelectionCoefficients
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.DysonTraceSeries
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.QuarticInteraction
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse

set_option linter.style.header false

/-!
# Perturbative two-point series

The order-`n` mixed time-ordered explicit-μ Gibbs coefficients of `DysonCoefficient.lean`
are assembled into formal power series in the coupling. The connected coefficient is owned by the integration
layer; this module only packages coefficient-level data into formal power series and performs
partition-function normalization.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- **The explicit-μ perturbative two-point series** of mixed time-ordered finite Gibbs expectations. -/
noncomputable def twoPointDysonSeries (ε : Mode → ℝ) (β μ : ℝ)
    (g : QuarticVertexLabel Mode → ℂ) (i j : Mode) (τ τ' : ℝ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => twoPointDysonCoefficient (n := n) ε β μ g i j τ τ'

/-- **The μ = 0 partition-function-normalized two-point series**: the two-point series divided by the partition series
of the same interaction, normalized to constant coefficient one.

The division is by the *normalized* partition series because the two-point coefficients are already
free Gibbs **expectations** — the free partition function has been divided out of each of them, so
only the interacting vacuum contributions remain to be cancelled. -/
noncomputable def partitionFunctionNormalizedTwoPointDysonSeries (ε : Mode → ℝ) (β : ℝ)
    (g : QuarticVertexLabel Mode → ℂ) (i j : Mode) (τ τ' : ℝ) : PowerSeries ℂ :=
  twoPointDysonSeries ε β 0 g i j τ τ' *
    (PowerSeries.normalizeByConstantCoeff
      (Common.dysonTraceSeries (fermionEnergy ε) β (quarticInteraction g)))⁻¹

/-- **The connected perturbative two-point series.** -/
noncomputable def connectedTwoPointDysonSeries (ε : Mode → ℝ) (β : ℝ)
    (g : QuarticVertexLabel Mode → ℂ) (i j : Mode) (τ τ' : ℝ) : PowerSeries ℂ :=
  PowerSeries.mk (connectedTwoPointDysonCoefficient ε β g i j τ τ')

/-- The unamputated 1PI two-point diagram series. This is not yet the proper self-energy:
the Dyson identification requires external-leg amputation and a 1PI insertion decomposition. -/
noncomputable def oneParticleIrreducibleTwoPointDysonSeries (ε : Mode → ℝ) (β : ℝ)
    (g : QuarticVertexLabel Mode → ℂ) (i j : Mode) (τ τ' : ℝ) : PowerSeries ℂ :=
  PowerSeries.mk (oneParticleIrreducibleTwoPointDysonCoefficient ε β g i j τ τ')

end Fermionic
end SecondQuantization
