import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Integration.DysonCoefficient
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Integration.DiagramIntegral
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Core.OneParticleIrreducible
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.DysonTraceSeries
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.QuarticInteraction
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse

set_option linter.style.header false

/-!
# Perturbative two-point series

The order-`n` mixed time-ordered explicit-μ Gibbs coefficients of `DysonCoefficient.lean`
are assembled into formal power series in the coupling. Connected and proper 1PI coefficients select the corresponding integrated diagrams. The series
package also performs partition-function normalization.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

open Classical in
/-- The order-`n` coefficient of the connected two-point series: the integrated Dyson amplitudes of
the externally connected diagrams only. The Gibbs state uses ε − μ; the
external-field factor restores physical-H evolution from the effective dispersion. -/
noncomputable def connectedTwoPointDysonCoefficient (ε : Mode → ℝ) (β μ : ℝ)
    (g : QuarticVertexLabel Mode → ℂ) (i j : Mode) (τ τ' : ℝ) (n : ℕ) : ℂ :=
  twoPointChemicalPotentialFactor μ τ τ' *
    ∑ d ∈ (Finset.univ : Finset (FixedExternalTwoPointWickDiagram Mode n i j)).filter
        fun d => d.1.IsExternallyConnected,
      d.dysonAmplitude (fun k => ε k - μ) β g τ τ'

open Classical in
/-- The order-`n` integrated two-point contribution from proper 1PI pairing diagrams. -/
noncomputable def oneParticleIrreducibleTwoPointDysonCoefficient (ε : Mode → ℝ) (β : ℝ)
    (g : QuarticVertexLabel Mode → ℂ) (i j : Mode) (τ τ' : ℝ) (n : ℕ) : ℂ :=
  ∑ d ∈ (Finset.univ : Finset (FixedExternalTwoPointWickDiagram Mode n i j)).filter
      fun d => d.1.IsOneParticleIrreducible,
    d.dysonAmplitude ε β g τ τ'

/-- **The explicit-μ perturbative two-point series** of mixed time-ordered finite Gibbs expectations. -/
noncomputable def twoPointDysonSeries (ε : Mode → ℝ) (β μ : ℝ)
    (g : QuarticVertexLabel Mode → ℂ) (i j : Mode) (τ τ' : ℝ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => twoPointDysonCoefficient (n := n) ε β μ g i j τ τ'

/-- **The explicit-μ partition-function-normalized two-point series**: the two-point series divided by the partition series
of the same number-conserving interaction at effective dispersion ε − μ, normalized to
constant coefficient one. Physical field evolution continues to use ε.

The division is by the *normalized* partition series because the two-point coefficients are already
free Gibbs **expectations** — the free partition function has been divided out of each of them, so
only the interacting vacuum contributions remain to be cancelled. -/
noncomputable def partitionFunctionNormalizedTwoPointDysonSeries (ε : Mode → ℝ) (β μ : ℝ)
    (g : QuarticVertexLabel Mode → ℂ) (i j : Mode) (τ τ' : ℝ) : PowerSeries ℂ :=
  twoPointDysonSeries ε β μ g i j τ τ' *
    (PowerSeries.normalizeByConstantCoeff
      (Common.dysonTraceSeries (fermionEnergy (fun k => ε k - μ)) β (quarticInteraction g)))⁻¹

/-- **The connected perturbative two-point series.** -/
noncomputable def connectedTwoPointDysonSeries (ε : Mode → ℝ) (β μ : ℝ)
    (g : QuarticVertexLabel Mode → ℂ) (i j : Mode) (τ τ' : ℝ) : PowerSeries ℂ :=
  PowerSeries.mk (connectedTwoPointDysonCoefficient ε β μ g i j τ τ')

/-- The unamputated 1PI two-point diagram series. This is not yet the proper self-energy:
the Dyson identification requires external-leg amputation and a 1PI insertion decomposition. -/
noncomputable def oneParticleIrreducibleTwoPointDysonSeries (ε : Mode → ℝ) (β : ℝ)
    (g : QuarticVertexLabel Mode → ℂ) (i j : Mode) (τ τ' : ℝ) : PowerSeries ℂ :=
  PowerSeries.mk (oneParticleIrreducibleTwoPointDysonCoefficient ε β g i j τ τ')

end Fermionic
end SecondQuantization
